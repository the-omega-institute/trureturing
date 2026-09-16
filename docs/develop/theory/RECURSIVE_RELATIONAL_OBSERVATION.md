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
## 16. 增补·Zeckendorf 低位读数的紧致增强障碍与加法闭图

**定义 16.0（数字观察、平移区分与加法闭图）。** 取 $\mathbb N=\{0,1,2,\ldots\}$，并置
$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,\qquad
\phi=\frac{1+\sqrt5}{2},\qquad \alpha=\phi^{-1},\qquad r=-\alpha.
$$
令 $Z(n)$ 为 $n$ 的有限 Zeckendorf 规范字按低位到高位排列后补零所得的无限字，包括 $Z(0)=0_K$。设
$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ 对所有 }j\},\qquad
D_L=\{\text{长度为 }L\text{ 的合法二值字}\},
$$
$$
\pi_L(x)=(x_0,\ldots,x_{L-1}),\qquad q_L=\pi_L\circ Z,\qquad
\delta_j(x)=x_j.
$$
其中 $D_0$ 仅含空字，将 $D_1$ 与 $\{0,1\}$ 自然等同，故 $q_1(n)=Z(n)_0$。各数字空间取乘积拓扑，有限读数空间取离散拓扑。沿用带符号相位
$$
d_K(x,y)=\sum_{j\ge0}2^{-j-1}|x_j-y_j|,\qquad
F(x)=\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j,
$$
$$
\mathbb T=\mathbb R/\mathbb Z,\qquad H(x)=[F(x)],\qquad
\gamma(n)=[n\phi],\qquad E=\{[-m\phi]:m\ge1\}.
$$
对有限离散集 $D$ 和函数 $f:\mathbb N\to D$，定义平移区分关系
$$
n\equiv_f m\quad\Longleftrightarrow\quad
\forall k\in\mathbb N,\ f(n+k)=f(m+k).
$$
称 $f$ 最终周期，若存在 $t\ge0$、$d\ge1$，使所有 $n\ge t$ 满足 $f(n+d)=f(n)$。定义
$$
\Gamma=\overline{\{(Z(n),Z(m),Z(n+m)):n,m\in\mathbb N\}}^{\,K^3},\qquad
\Gamma(x,y)=\{z\in K:(x,y,z)\in\Gamma\}.
$$

**定理 16.1（有限读数的紧致实现判据与忠实增强不可能性）。** 对任意有限离散集 $D$ 和 $f:\mathbb N\to D$，下列条件等价：

（甲）$f$ 最终周期。

（乙）存在紧致 Hausdorff 空间 $X$、映射 $j:\mathbb N\to X$ 和联合连续函数 $B:X\times X\to D$，使
$$
B(j(n),j(m))=f(n+m)\qquad(n,m\in\mathbb N).
$$
这里不要求 $j$ 单射、连续或具有稠密像。

（丙）存在有限离散交换幺半群 $M$、满射幺半群同态 $\iota:(\mathbb N,+)\to M$ 和函数 $h:M\to D$，使 $h\circ\iota=f$。

因此，若紧致 Hausdorff 空间 $L$ 上存在联合连续 $A:L\times L\to L$、连续 $h:L\to D$ 和映射 $j:\mathbb N\to L$，满足
$$
A(j(n),j(m))=j(n+m),\qquad h(j(n))=f(n),
$$
则 $f$ 必最终周期。若另有 $j[\mathbb N]$ 稠密，$A$ 自动满足结合律、交换律，并以 $j(0)$ 为单位。

对于 $f=q_1$，上述实现全部不存在。尤其不存在紧致 Hausdorff 空间 $L$、稠密映射 $j:\mathbb N\to L$、连续 $P:L\to K$ 及联合连续 $A:L\times L\to L$ 同时满足
$$
P\circ j=Z,\qquad A(j(n),j(m))=j(n+m).
$$
此外，$\equiv_{q_1}$ 恰为相等关系；因而任何包含于 $\ker q_1$ 的加法同余都只能是相等关系。

**证明。** 先证明乙推出甲。固定 $x\in X$。对每个 $y\in X$，由 $B$ 连续及 $D$ 离散，可取开邻域 $U_y\ni x$、$V_y\ni y$，使 $B$ 在 $U_y\times V_y$ 上恒等于 $B(x,y)$。紧致性给有限子覆盖 $V_{y_1},\ldots,V_{y_s}$。置
$$
U_x=\bigcap_{i=1}^{s}U_{y_i}.
$$
若 $x'\in U_x$、$z\in X$，选择 $i$ 使 $z\in V_{y_i}$，则
$$
B(x',z)=B(x,y_i)=B(x,z).
$$
故整行函数 $B(x',\cdot)$ 在 $U_x$ 内不变。再对开覆盖 $\{U_x:x\in X\}$ 使用紧致性，得到整行函数 $B(x,\cdot)$ 仅有有限多个。于是存在整数 $a<b$，使
$$
B(j(a),z)=B(j(b),z)\qquad(z\in X).
$$
取 $z=j(k)$，得到 $f(a+k)=f(b+k)$ 对所有 $k\ge0$ 成立。这就是从 $a$ 开始、以 $b-a$ 为周期的最终周期性。此论证没有假设 $X$ 零维，也没有使用紧空间的序列紧性。[^rro16_compact]

若甲成立，定义
$$
n\mathrel{R_{t,d}}m\quad\Longleftrightarrow\quad
n=m\ \lor\ \bigl(n,m\ge t\text{ 且 }n\equiv m\pmod d\bigr).
$$
它是加法同余：等价的两数同时加上任意 $k\ge0$ 后，或者仍相等，或者仍处于阈值以上并有相同模 $d$ 剩余类；依次替换两个槽位即得双槽相容性。商集有 $t+d$ 个元素，运算 $[n]+[m]=[n+m]$ 定义良好。最终周期性保证 $h([n])=f(n)$ 定义良好，给出丙。这给出阈值—周期商的有限实现。[^rro16_unary] 丙推出乙，只需取 $X=M$、$j=\iota$、$B(s,t)=h(s+t)$；有限离散空间上的这些映射连续。

若给定 $L,A,h,j$，取 $B=h\circ A$ 即适用乙。稠密情形下，结合律两边是 $L^3\to L$ 的连续映射，且在稠密集 $j[\mathbb N]^3$ 上相等；Hausdorff 性使其相等集合闭，故处处相等。交换律及左右单位律同理分别在 $L^2$ 与 $L$ 上由稠密性延拓。这也证明紧致拓扑幺半群上的连续有限读数沿单生成轨道必最终周期。

现在证明 $q_1$ 不最终周期。长度为 $L$ 的合法字按权值求和，恰与整数区间 $[0,G_L)\cap\mathbb N$ 双射。对于 $L=0,1$ 可直接验证；对于 $L\ge2$，最高位为零的字给出区间 $[0,G_{L-1})$，最高位为一则次高位被迫为零，给出区间
$$
G_{L-1}+[0,G_{L-2})=[G_{L-1},G_L).
$$
两个区间不交，归纳即得双射。最低位为一的字以 $10$ 开始，余下 $L-2$ 位任取合法字，所以对 $L\ge2$，
$$
\sum_{n=0}^{G_L-1}q_1(n)=G_{L-2}.
$$
由初值和递推式验证
$$
G_L=\frac{\phi^{L+2}-(-\alpha)^{L+2}}{\sqrt5},
$$
从而
$$
\lim_{L\to\infty}\frac1{G_L}\sum_{n=0}^{G_L-1}q_1(n)
=\alpha^2=\frac{3-\sqrt5}{2}\notin\mathbb Q.
$$
若一个二值序列从 $t$ 开始具有周期 $d$，且一周期中有 $c$ 个一，则把任意长初段分成初始段、完整周期和不足一周期的余段，得到其平均值趋于 $c/d$；初始段和余段引起的误差分子有界。因此其在长度 $G_L$ 上的平均值也必须趋于同一有理数，矛盾。这里所需且已证明的是沿 $G_L$ 的平均值极限。[^rro16_count]

因此 $q_1$ 不满足甲。若存在所列 $P,A,j$，取 $h=\delta_0\circ P$ 即与已经证明的不可能性矛盾。

最后，对任意 $f$，关系 $\equiv_f$ 是包含于 $\ker f$ 的加法同余：等价关系性质逐项成立，而把两数同时平移 $a$ 后的测试 $k$ 就是原来的测试 $a+k$。任意加法同余 $R\subseteq\ker f$ 都满足
$$
n\mathrel Rm\Longrightarrow n+k\mathrel Rm+k
\Longrightarrow f(n+k)=f(m+k),
$$
所以 $R\subseteq\equiv_f$。若有 $n<m$ 且 $n\equiv_fm$，则 $f$ 从 $n$ 开始以 $m-n$ 为周期。对不最终周期的 $q_1$ 不可能出现这样的不同元素，故 $\equiv_{q_1}$ 是相等关系，关于加法同余的断言随即成立。证毕。

**推论 16.2（辅助读数的边界、完成契约与素数轴转移）。** 下列结论成立。

（甲）令 $I_0$ 为任意集合，$C_i$ 为紧致 Hausdorff 空间，$d_i:\mathbb N\to C_i$ 为任意辅助读数。置
$$
j_d(n)=(Z(n),(d_i(n))_{i\in I_0}),\qquad
L_d=\overline{j_d[\mathbb N]}^{\,K\times\prod_{i\in I_0}C_i}.
$$
则 $L_d$ 紧致，向 $K$ 的投影满射，但不存在延拓自然加法的联合连续 $A:L_d^2\to L_d$。即使只要求联合连续 $B:L_d^2\to\{0,1\}$ 满足
$$
B(j_d(n),j_d(m))=q_1(n+m),
$$
仍不可能。此结论包括任意多个有限标签、任意紧值标签，以及标签不连续于原数字核心拓扑的情形。更直接地，不存在有限集 $C$ 和函数 $c:\mathbb N\to C$、$g:C^2\to\{0,1\}$，使 $g(c(n),c(m))=q_1(n+m)$ 对全部 $n,m$ 成立。

（乙）令
$$
u=(10)^\omega,\qquad v=(01)^\omega,\qquad
a_k=\sum_{j=0}^{k}G_{2j},\qquad b_k=G_{2k},\qquad c_k=a_k+b_k.
$$
则
$$
a_k=G_{2k+1}-1,\qquad
c_k=G_{2k+2}-1=\sum_{j=0}^{k}G_{2j+1}.
$$
对每个 $m\ge0$ 及 $2k\ge m$，两输入对 $(0,a_k)$、$(b_k,a_k)$ 的每个槽位具有相同 $q_m$ 读数，而和的 $q_1$ 读数分别为一和零。并且
$$
Z(a_k)\longrightarrow u,\qquad Z(b_k)\longrightarrow0_K,\qquad Z(c_k)\longrightarrow v,
$$
$$
(0_K,u,u),(0_K,u,v)\in\Gamma.
$$

（丙）圆周上的加法和嵌入 $\gamma$ 保留自然加法，却不保留数字读数的全局连续延拓。更精确地，$\gamma$ 单射，数字拓扑与相位拓扑在 $\mathbb N$ 上相同；然而，对每个 $L\ge1$，不存在函数 $\psi:\mathbb T\to D_L$ 使 $\pi_L=\psi\circ H$，甚至不要求 $\psi$ 连续也不行。每个单独坐标 $\delta_j$ 同样不能经 $H$ 因子化。相反，核心上的函数
$$
\gamma(n)\longmapsto q_L(n)
$$
定义良好且连续，但没有连续的全圆周延拓。度量
$$
d_{\rm digit}(n,m)=d_K(Z(n),Z(m)),\qquad
d_{\rm phase}(n,m)=\rho(\gamma(n),\gamma(m)),
$$
其中 $\rho([s],[t])=\min_{k\in\mathbb Z}|s-t-k|$，给出不同一致结构，完成分别为 $K$ 和 $\mathbb T$。

因此，保留联合连续加法和紧致性时，必须舍弃至少这个原始低位读数的全局连续恢复；若保留原数字读数和自然加法，则可以留在非紧的数字核心；若保留紧载体 $K$ 和所有数字，则固定平移 $T^h$ 仍可连续，但不能把这些固定平移合成为延拓自然加法的联合连续二元运算。[^rro16_phase]

（丁）令 $\mathcal P$ 为全部素数的集合，对 $N\in\mathbb N_{>0}$ 记 $\nu_p(N)$ 为素数 $p$ 的指数，并定义
$$
\eta(N)=(Z(\nu_p(N)))_{p\in\mathcal P}\in K^{\mathcal P}.
$$
其实际像准确为
$$
\eta[\mathbb N_{>0}]
=\{x\in K^{\mathcal P}:x_p\in Z[\mathbb N]\text{ 对每个 }p,
\ \{p:x_p\ne0_K\}\text{ 有限}\}.
$$
对有限素数集 $S$ 和逐行有限精度 $\ell:S\to\mathbb N$，令
$$
Q_{S,\ell}(N)=(q_{\ell(p)}(\nu_p(N)))_{p\in S}.
$$
其实际像恰为有限集 $\prod_{p\in S}D_{\ell(p)}$。按扩大 $S$、提高各行精度组成的逆系统，其逆极限为 $K^{\mathcal P}$，且 $\eta[\mathbb N_{>0}]$ 在其中稠密。无限完整素数表不是这个系统的一个有限层；有限素数窗口中一条无限精度行也不是有限层。

固定素数 $p$ 后，$n\mapsto p^n$ 是 $(\mathbb N,+)$ 到乘法子幺半群 $\{p^n:n\ge0\}$ 的同构。不存在紧致 Hausdorff 空间 $M$、映射 $j:\mathbb N_{>0}\to M$、联合连续乘法 $\mu:M^2\to M$ 和连续 $h_p:M\to\{0,1\}$ 同时满足
$$
\mu(j(N),j(R))=j(NR),\qquad h_p(j(N))=q_1(\nu_p(N)).
$$
这里甚至不要求 $j[\mathbb N_{>0}]$ 稠密。

**证明。** 甲中，Tychonoff 定理和闭子空间的紧致性给出 $L_d$ 紧致。投影像是 $K$ 中含有稠密集 $Z[\mathbb N]$ 的紧集，因 $K$ Hausdorff 而闭，所以投影满射。投影的最低位读数连续，故定理16.1排除 $A$；该定理的乙条件直接排除 $B$。对于有限摘要 $c$，若 $c(n)=c(m)$，则对所有 $k$，
$$
q_1(n+k)=g(c(n),c(k))=g(c(m),c(k))=q_1(m+k).
$$
由 $\equiv_{q_1}$ 为相等关系，必有 $n=m$。这迫使 $c$ 将无限集单射到有限集，矛盾。

乙中的偶位和恒等式在 $k=0$ 时为 $G_0=G_1-1$；若对 $k$ 成立，则加上 $G_{2k+2}$ 并使用递推式，得到下一项。奇位和同理从 $G_1=G_2-1$ 归纳。再由
$$
a_k+b_k=G_{2k+1}+G_{2k}-1=G_{2k+2}-1
$$
得到全部恒等式。显示的偶位和、奇位和及单个权值都是合法规范字，故其补零字就是相应的 $Z$ 值。若 $2k\ge m$，$Z(b_k)$ 的前 $m$ 位均为零；$Z(a_k)$ 的最低位为一，$Z(c_k)$ 的最低位为零。逐坐标最终稳定给出三个极限。原加法图中的
$$
(Z(0),Z(a_k),Z(a_k)),\qquad
(Z(b_k),Z(a_k),Z(c_k))
$$
分别趋于所列三元组，故它们属于 $\Gamma$。特别 $k=2$ 时，$a_2=1+3+8=12$、$b_2=8$、$c_2=2+5+13=20$。

丙中使用既有相位结论：$K$ 紧致，$Z[\mathbb N]$ 稠密，$H$ 连续满射，$H\circ Z=\gamma$；$H$ 的二点纤维恰位于 $E$，自然轨道上的纤维为单点；并且 $H(u)=H(v)=[-\phi]$。[^rro16_phase] 由 $\phi$ 无理，$\gamma$ 单射；由 $H$ 满射及核心稠密，$\gamma[\mathbb N]$ 稠密。

连续性 $H\circ Z=\gamma$ 给相位拓扑包含于数字拓扑。反之，设 $U\subseteq K$ 开且 $Z(n)\in U$。单点纤维性质保证 $\gamma(n)\notin H(K\setminus U)$。后者为紧闭集，所以
$$
V=\mathbb T\setminus H(K\setminus U)
$$
是包含 $\gamma(n)$ 的开集，且 $H^{-1}(V)\subseteq U$。拉回核心即得反向拓扑包含。于是核心数字读数经 $\gamma$ 表示后连续。

但 $u_j\ne v_j$ 对每个 $j$ 成立，而 $H(u)=H(v)$，故任何 $\delta_j$、任何正长度前缀 $\pi_L$ 都不能经 $H$ 因子化。圆周连通，连续映射到有限离散空间必为常函数；核心 $q_L$ 对 $L\ge1$ 非常值，故不存在其连续全圆周延拓。这里 $\gamma$ 在核心上的单射性与边界处数字不能恢复是不同断言。

紧空间上的连续映射 $H$ 一致连续，因此恒等映射从数字一致结构到相位一致结构一致连续。乙中的两列却满足
$$
\rho(\gamma(a_k),\gamma(c_k))\longrightarrow0,\qquad
d_K(Z(a_k),Z(c_k))=1-2^{-(2k+2)}\longrightarrow1.
$$
第一式来自共同极限相位，第二式来自前 $2k+2$ 位逐位相反、其余均为零。故反向恒等映射不一致连续。两个紧度量空间都完备，并分别含有相应稠密等距核心，因而是所列两个度量的完成。

相位核心在圆周加法下封闭，且 $\gamma(n+m)=\gamma(n)+\gamma(m)$；故加法在相位核心连续，也就在相同的数字核心拓扑连续。数字核心不是紧空间：它在 Hausdorff 紧空间 $K$ 中稠密且不含 $u$，若紧则必闭而等于 $K$，矛盾。另一方面，既有连续后继 $T$ 的固定迭代 $T^h$ 延拓固定自然平移；其存在不满足定理16.1所要求的二元联合连续运算契约。[^rro16_phase]

丁中，由素因子分解的存在唯一性，每个正整数只有有限个非零素数指数；每个指数有唯一有限规范行。因此 $\eta$ 单射并落入显示的实际像。反之，对显示集合中的表，逐个非零行解码为自然指数 $e_p$，有限乘积 $\prod_p p^{e_p}$ 恢复原表，证明像的准确性。

给定任意 $(d_p)_{p\in S}\in\prod_{p\in S}D_{\ell(p)}$，令
$$
e_p=\sum_{j<\ell(p)}G_j(d_p)_j,\qquad N=\prod_{p\in S}p^{e_p}.
$$
合法字补零仍为规范字，故 $Q_{S,\ell}(N)=(d_p)_{p\in S}$，包括空窗口与零精度情形。这证明每个有限层的实际满性。兼容的全部有限窗口在每个素数轴上给出唯一无限合法行，反之无限行表给出兼容窗口；这些对应保持有限柱集，故得到拓扑逆极限 $K^{\mathcal P}$。有限层满性又使每个非空基本柱集都遇到实际像，证明稠密性。

在固定 $p$ 的幂子幺半群上，$\eta(p^n)$ 只有 $p$ 行可能非零，该行为 $Z(n)$；其闭包是仅允许 $p$ 行任取 $K$、其余行全零的子空间。若所列 $M,j,\mu,h_p$ 存在，令
$$
j_p(n)=j(p^n),\qquad B=h_p\circ\mu.
$$
则
$$
B(j_p(n),j_p(m))=q_1(\nu_p(p^{n+m}))=q_1(n+m),
$$
与定理16.1矛盾。

有限窗口上的逃逸也由同一证据直接得到：给定 $S,\ell$，取 $m=\ell(p)$ 当 $p\in S$，否则取 $m=0$，再取 $2k\ge m$。两输入对
$$
(1,p^{a_k}),\qquad (p^{b_k},p^{a_k})
$$
在两个槽位的 $Q_{S,\ell}$ 读数分别相同，但两个乘积的 $p$ 行最低位分别为 $q_1(a_k)=1$ 与 $q_1(c_k)=0$。所有其他素数行均为零。证毕。

**定义 16.3（二点相位纤维的定向标记）。** 置
$$
a=-\alpha,\qquad b=\alpha^2,\qquad I=[a,b],\qquad c_*=-\alpha^3,\qquad \theta_*=[-\phi].
$$
将无限合法字唯一解析为块 $0$、$10$。对有限块字 $w$，记展开后的数字长度为 $L(w)$，并置
$$
S_w=\sum_{j<L(w)}(-1)^{j+1}\alpha^{j+2}w_j,\qquad
f_w(t)=S_w+r^{L(w)}t.
$$
空块字允许出现。既有实相位纤维分类给出：端点纤维分别为 $\{u\}$、$\{v\}$；每个内部二点纤维唯一写成
$$
F^{-1}(\{f_w(c_*)\})=\{w0v,w10v\}.
$$
相应内部相位恰遍历 $E\setminus\{\theta_*\}$。[^rro16_phase] 定义
$$
z_{\theta_*}^{+1}=u,\qquad z_{\theta_*}^{-1}=v.
$$
对 $\theta=[f_w(c_*)]\ne\theta_*$，定义
$$
(z_\theta^{+1},z_\theta^{-1})=
\begin{cases}
(w0v,w10v),&L(w)\text{ 为偶数},\\
(w10v,w0v),&L(w)\text{ 为奇数}.
\end{cases}
$$
连接记号均按低位到高位解释。最后置
$$
\mathcal S(x)=
\begin{cases}
\{+1\},&H(x)\in E,\ x=z_{H(x)}^{+1},\\
\{-1\},&H(x)\in E,\ x=z_{H(x)}^{-1},\\
\{-1,+1\},&H(x)\notin E.
\end{cases}
$$

**定理 16.4（加法闭图的完整输入纤维分类）。** 对任意 $x,y\in K$，置 $\theta=H(x)+H(y)$。则
$$
\Gamma(x,y)=
\begin{cases}
H^{-1}(\{\theta\}),&\theta\notin E,\\
\{z_\theta^{+1}\},&\theta\in E,\ \mathcal S(x)=\mathcal S(y)=\{+1\},\\
\{z_\theta^{-1}\},&\theta\in E,\ \mathcal S(x)=\mathcal S(y)=\{-1\},\\
\{z_\theta^{+1},z_\theta^{-1}\},&\theta\in E\text{ 且不属于上述两种同号情形}.
\end{cases}
$$
第一种情形的纤维恰有一点。特别每个输入纤维非空且至多有两点，且
$$
\Gamma(Z(n),Z(m))=\{Z(n+m)\}\qquad(n,m\in\mathbb N).
$$
但是
$$
\Gamma\subsetneq\{(x,y,z)\in K^3:H(z)=H(x)+H(y)\}.
$$
更具体地，以 $0v$、$10v$ 表示有限字与 $v$ 的连接，有
$$
\Gamma(0_K,u)=\{u,v\},\qquad
\Gamma(u,u)=\{0v\},\qquad
\Gamma(v,v)=\{10v\},\qquad
\Gamma(u,v)=\{0v,10v\}.
$$
所以闭图保留全部核心加法，却不满足以 $0_K$ 为单位的集合值单位律 $\Gamma(0_K,x)=\{x\}$。

**证明。** 先证明定向标记的逼近性质。若 $H(x)=\beta\notin E$，则对任何自然数列 $n_i$，
$$
\gamma(n_i)\longrightarrow\beta\quad\Longrightarrow\quad Z(n_i)\longrightarrow x.
$$
事实上，$K$ 紧致且可度量；任意聚点都由 $H$ 连续性落在单点纤维 $H^{-1}(\{\beta\})=\{x\}$。若原序列不趋于 $x$，可在某个固定邻域外取子序列，再取收敛子列，得到另一个聚点，矛盾。

对于 $\beta\in E$，若
$$
\gamma(n_i)=\beta+[\varepsilon_i],\qquad
0<|\varepsilon_i|<\tfrac12,\qquad \varepsilon_i\longrightarrow0,
$$
则对每个 $s\in\{-1,+1\}$，有准确的单侧等价
$$
Z(n_i)\longrightarrow z_\beta^s
\quad\Longleftrightarrow\quad
\operatorname{sgn}(\varepsilon_i)=s\text{ 最终成立}.
$$
为证此式，先取 $\beta=\theta_*$。由于 $F(Z(n_i))\in(a,b)$ 且 $b-a=1$，正的小偏移对应代表 $a+\varepsilon_i$，负的小偏移对应代表 $b+\varepsilon_i$。实端点纤维的唯一性与上述紧致聚点论证分别给出极限 $u$ 和 $v$。反之，趋于 $u$ 或 $v$ 时，连续实函数 $F$ 分别趋于 $a$ 或 $b$，且有限核心不达到端点，故偏移最终分别为正或负。

再取内部二点相位 $\beta=[c]$，其中 $c=f_w(c_*)\in(a,b)$。拆分定义 $F$ 的级数可得
$$
F(wt)=f_w(F(t)),\qquad
f_0(I)=[c_*,b],\qquad f_{10}(I)=[a,c_*].
$$
由 $F(K)=I$，两个互不相交的开闭柱集 $[w0]_K$、$[w10]_K$ 的实值域分别为
$$
f_w([c_*,b]),\qquad f_w([a,c_*]).
$$
它们位于 $c$ 的两侧。若 $L(w)$ 为偶数，前者在右、后者在左；若为奇数，则方向交换。这正是定义16.3的标记。对充分小的局部偏移，相位差就是实代表与 $c$ 的差，因为 $c$ 位于 $(a,b)$ 内。

任何聚点只能是 $w0v$ 或 $w10v$。若偏移始终取指定符号，却有子列趋于反号标记，该子列最终进入反号标记的开闭柱集，其实值域方向与偏移符号矛盾。因此只有指定标记能成为聚点，紧致性给出整列收敛。反之，若 $Z(n_i)$ 趋于一个标记，它最终进入对应单侧柱集。自然轨道不遇到 $E$，所以偏移不能等于零，必最终具有该侧符号。单侧等价得证。

现在证明分类的必要性。若 $(x,y,z)\in\Gamma$，由 $K^3$ 可度量，存在同一列自然数对 $(n_i,m_i)$，使
$$
(Z(n_i),Z(m_i),Z(n_i+m_i))\longrightarrow(x,y,z).
$$
连续性和核心上的加法相位恒等式给出
$$
H(z)=H(x)+H(y)=\theta.
$$
故 $\Gamma(x,y)\subseteq H^{-1}(\{\theta\})$。若 $\theta\notin E$，可能输出至多一个。若两输入都被迫为正号标记，分别写其趋零局部偏移为 $\varepsilon_i,\delta_i$，单侧等价保证二者最终均正；它们之和仍正，并且最终绝对值小于 $1/2$。由于
$$
\gamma(n_i+m_i)=\theta+[\varepsilon_i+\delta_i],
$$
输出只能趋于 $z_\theta^{+1}$。两个负号输入完全同理。其余情形只剩该相位的两个标记，不会出现第三个输出。

下面证明每个列出的输出都由共同的自然数对序列实现。若 $\theta\notin E$，可分别用截断字选择 $n_i,m_i$ 使 $Z(n_i)\to x$、$Z(m_i)\to y$。和的相位趋于 $\theta$，单点纤维的逼近性质保证整列 $Z(n_i+m_i)$ 趋于该唯一输出。

设 $\theta\in E$，并固定分类式允许的目标符号 $s\in\{-1,+1\}$。允许性意味着不是两个输入都被迫取 $-s$，因而至少一个输入允许符号 $s$。交换两输入后，可设 $s\in\mathcal S(x)$。任取 $t\in\mathcal S(y)$，令
$$
\tau_i=\frac1{100(i+1)},\qquad
I_i=(3s\tau_i-\tau_i/4,\ 3s\tau_i+\tau_i/4),\qquad
J_i=(t\tau_i-\tau_i/4,\ t\tau_i+\tau_i/4).
$$
圆周自然轨道稠密，所以可同时选择 $n_i,m_i\in\mathbb N$，使
$$
\gamma(n_i)\in H(x)+[I_i],\qquad
\gamma(m_i)\in H(y)+[J_i].
$$
这里 $[I_i]=\{[a]:a\in I_i\}$，另一个区间同理。取相应实偏移 $\varepsilon_i\in I_i$、$\delta_i\in J_i$。它们趋于零且分别具有允许的符号 $s,t$；对非分裂输入使用单点纤维逼近性质，对分裂输入使用单侧等价，得到
$$
Z(n_i)\longrightarrow x,\qquad Z(m_i)\longrightarrow y.
$$
而 $\varepsilon_i+\delta_i$ 的中心为 $(3s+t)\tau_i$，与中心的距离小于 $\tau_i/2$。因 $3s+t$ 与 $s$ 同号且绝对值至少为二，偏移和始终具有符号 $s$，趋于零且绝对值小于 $1/2$。再次应用单侧等价，得到
$$
Z(n_i+m_i)\longrightarrow z_\theta^s.
$$
这构造的是同一对输入序列及其实际和，不是三条彼此无关的相位逼近。所有允许输出均已实现，分类式得证。

自然数核心输入的和相位是 $\gamma(n+m)\notin E$，其纤维为 $\{Z(n+m)\}$，给出核心精确性。最后，$H(0_K)=0$，$H(u)=H(v)=\theta_*$，且
$$
2\theta_*=[-2\phi]=[c_*],\qquad
z_{[-2\phi]}^{+1}=0v,\qquad z_{[-2\phi]}^{-1}=10v.
$$
将空块字及符号 $\mathcal S(0_K)=\{-1,+1\}$、$\mathcal S(u)=\{+1\}$、$\mathcal S(v)=\{-1\}$ 代入分类式，即得四个显示的输入纤维。特别 $(u,u,10v)$ 满足相位等式，却不属于 $\Gamma$，证明严格包含；$\Gamma(0_K,u)=\{u,v\}$ 则否定所述单位律。证毕。

[^rro16_compact]: Jorge Almeida, Herman Goulet-Ouellet, Ondřej Klíma, *What makes a Stone topological algebra Profinite*, Algebra universalis 84, article 6 (2023), DOI: [10.1007/s00012-023-00804-w](https://link.springer.com/article/10.1007/s00012-023-00804-w)，尤见第3节 Lemma 3.1（正式版第7页）、第5.1节（第10页）及 Theorem 5.16（第18页）。定理16.1中所需的有限值双变量特例已由开覆盖完整证明，不以载体为 Stone 空间为前提。

[^rro16_unary]: James East, Nik Ruškuc, *Classification of congruences of twisted partition monoids*, arXiv:[2010.04392v3](https://arxiv.org/html/2010.04392v3#S2.SS1)，第2.1节关于自然数加法同余的未编号段落；亦见本卷定理11.2的自然数加法同余分类。

[^rro16_count]: Hung Viet Chu, *The Fibonacci Sequence and Schreier-Zeckendorf Sets*, Journal of Integer Sequences 22 (2019), arXiv:[1906.10962](https://arxiv.org/abs/1906.10962)。这里只用合法有限字的基本计数，所需递推及最低位计数已在定理16.1内证明。

[^rro16_phase]: *CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF*，第371—377节，特别是定理371.2、372.2—372.4、373.2、375.2—375.3与377.1；固定文本为提交 c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb 的 [Zeckendorf 理论卷](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)。

## 追加锚（本行以下为增补区）
## 17. 完整历史见证、可逆后继与选史障碍

**定义与假设 17.0（完整过去空间及 Zeckendorf 前置）。** 在 ZFC 中取 $\mathbb N=\{0,1,\ldots\}$。对非空紧致 Hausdorff 空间 $X$ 及连续满射 $f:X\to X$，定义
$$
\mathcal L_f=\{(x_0,x_1,\ldots)\in X^{\mathbb N}:f(x_{j+1})=x_j\text{ 对每个 }j\ge0\},
$$
赋予乘积空间的子空间拓扑，记 $p_j(x_0,x_1,\ldots)=x_j$、$P_f=p_0$，并定义候选演化
$$
U_f(x_0,x_1,\ldots)=(f(x_0),x_0,x_1,\ldots).
$$

具体情形沿用[前置卷第371–375节](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)的对象，在本节简记为
$$
\phi=\frac{1+\sqrt5}{2},\qquad \mathbb T=\mathbb R/\mathbb Z,\qquad K=\{x\in\{0,1\}^{\mathbb N}:x_ix_{i+1}=0\text{ 对所有 }i\ge0\}.
$$
$K$ 取乘积子空间拓扑。令 $G_0=1$、$G_1=2$、$G_{i+2}=G_{i+1}+G_i$，$Z(n)$ 为权值 $G_i$ 下低位起的有限 Zeckendorf 表示补零，$0=Z(0)$ 为全零状态，并记
$$
u=(10)^\omega,\qquad v=(01)^\omega,\qquad D=Z[\mathbb N],\qquad H(x)=\left[\sum_{i\ge0}(-1)^{i+1}\phi^{-i-2}x_i\right].
$$
$T$ 为前置卷定义375.1的首个相邻零后继：在首个 $00$ 的位置清零此前缀并置该位为一；无 $00$ 时输出 $0$。本节使用前置卷定理371.2、372.4、375.2–375.3的以下结论：$K$ 紧致可度量，$Z$ 单射且 $D$ 稠密；$T$ 连续满射，且
$$
TZ(n)=Z(n+1),\qquad T^{-1}(\{0\})=\{u,v\},
$$
每个非零状态的前驱唯一；$H$ 连续满射，且
$$
H(Z(n))=[n\phi],\qquad H(Tx)=H(x)+[\phi].
$$
$H$ 的二点纤维恰位于
$$
E_- =\{[-m\phi]:m\ge1\},
$$
其余相位的纤维均为单点，特别
$$
H^{-1}(\{[n\phi]\})=\{Z(n)\}\qquad(n\ge0).
$$
在此具体情形记 $L=\mathcal L_T$、$P=P_T$、$U=U_T$、$Q=H\circ P$，并置
$$
E_+=\{[n\phi]:n\ge0\},\qquad \mathcal O=\{[k\phi]:k\in\mathbb Z\}=E_-\cup E_+.
$$
由 $\phi$ 无理，$E_-\cap E_+=\varnothing$，且整数 $k$ 由相位 $[k\phi]$ 唯一确定。

**定理 17.1（主定理组：自然扩张及其准确泛性质）。** 对定义17.0的一般系统 $(X,f)$，$\mathcal L_f$ 非空、紧致且 Hausdorff；每个坐标投影 $p_j$ 都是连续满射，$P_f$ 还是闭映射及商映射。$U_f$ 是同胚，其逆为
$$
U_f^{-1}(x_0,x_1,x_2,\ldots)=(x_1,x_2,x_3,\ldots),
$$
并满足
$$
P_fU_f=fP_f,\qquad p_j=P_fU_f^{-j}.
$$

空间 $\mathcal L_f$ 连同各 $p_j$ 是逆系统
$$
X\xleftarrow{f}X\xleftarrow{f}X\xleftarrow{f}\cdots
$$
在拓扑空间范畴中的逆极限：若拓扑空间 $Y$ 上的连续映射 $a_j:Y\to X$ 满足 $fa_{j+1}=a_j$，则存在唯一连续映射 $a:Y\to\mathcal L_f$，使 $p_ja=a_j$ 对所有 $j$ 成立。

对于动力系统，令对象为三元组 $(Y,S,g)$，其中 $Y$ 是非空紧致 Hausdorff 空间，$S:Y\to Y$ 是同胚，$g:Y\to X$ 连续且 $gS=fg$。从 $(Y,S,g)$ 到 $(Y',S',g')$ 的箭头为满足
$$
hS=S'h,\qquad g'h=g
$$
的连续映射 $h:Y\to Y'$。在此范畴中，$(\mathcal L_f,U_f,P_f)$ 是终对象。准确地说，每个对象具有唯一的箭头
$$
\widetilde g:Y\longrightarrow\mathcal L_f,\qquad \widetilde g(y)=\bigl(g(y),g(S^{-1}y),g(S^{-2}y),\ldots\bigr),
$$
满足
$$
P_f\widetilde g=g,\qquad \widetilde gS=U_f\widetilde g.
$$
若 $g$ 满射，则 $\widetilde g$ 也满射。因此，进一步要求底映射 $g$ 和箭头 $h$ 均满射时，同一三元组仍是该可逆扩张范畴的终对象。这些性质将该扩张确定到唯一的、与底投影相容的动力学同胚。

一般逆极限的成熟框架见 Ingram–Mahavier，*Inverse Limits: From Continua to Chaos*，第2章“[Inverse Limits in a General Setting](https://doi.org/10.1007/978-1-4614-1797-2_2)”，第75–129页；上述移位同胚及自然扩张的动力学定位见 Boroński–Minc–Štimac，“[On conjugacy of natural extensions of one-dimensional maps](https://arxiv.org/html/2110.11440v1#S1)”，第1节，期刊 DOI：10.1017/etds.2022.62。

**证明。** 对每个 $j\ge0$，集合
$$
C_j=\{\xi\in X^{\mathbb N}:f(\xi_{j+1})=\xi_j\}
$$
是闭集：映射 $\xi\mapsto(f(\xi_{j+1}),\xi_j)$ 连续，而 Hausdorff 空间 $X$ 的对角线在 $X\times X$ 中闭。因此 $\mathcal L_f=\bigcap_{j\ge0}C_j$ 是紧致 Hausdorff 乘积空间 $X^{\mathbb N}$ 的闭子空间。

固定任意 $x\in X$。对 $N\ge0$ 置
$$
A_N(x)=\{\xi\in X^{\mathbb N}:\xi_0=x,\ f(\xi_{j+1})=\xi_j\text{ 对 }0\le j<N\}.
$$
这些是递减的闭集。由 $f^N$ 满射，存在 $y\in X$ 使 $f^N(y)=x$；令 $\xi_j=f^{N-j}(y)$ 对 $0\le j\le N$ 成立，并用任一固定状态填充其余坐标，即得 $A_N(x)$ 的元素。紧性与有限交性质给出
$$
\varnothing\ne\bigcap_{N\ge0}A_N(x)=P_f^{-1}(\{x\}).
$$
于是 $P_f$ 满射，且 $\mathcal L_f$ 非空。投影连续。若 $B\subseteq\mathcal L_f$ 闭，则 $B$ 紧，其像 $P_f(B)$ 在 Hausdorff 空间 $X$ 中闭，故 $P_f$ 是闭映射。连续闭满射是商映射：若 $P_f^{-1}(A)$ 闭，则 $A=P_f(P_f^{-1}(A))$ 闭，反向由连续性成立。

若 $\ell=(x_0,x_1,\ldots)\in\mathcal L_f$，则插入的首条关系为 $f(x_0)=f(x_0)$，其余关系来自 $\ell$，故 $U_f\ell\in\mathcal L_f$。删除首坐标也保留全部相容关系，定义映射 $V(\ell)=(x_1,x_2,\ldots)$。逐坐标检查得到
$$
VU_f=\operatorname{id}_{\mathcal L_f},\qquad U_fV=\operatorname{id}_{\mathcal L_f},
$$
其中第二式的首坐标使用 $f(x_1)=x_0$。两个映射的每个坐标函数均连续，所以两者连续，$U_f$ 为同胚且逆为 $V$。首坐标直接给出 $P_fU_f=fP_f$，反复删除首坐标给出 $p_j=P_fU_f^{-j}$；因此所有 $p_j$ 满射。

对于相容映射族 $(a_j)$，唯一可能的映射是 $a(y)=(a_j(y))_{j\ge0}$。相容性保证其值在 $\mathcal L_f$ 中，乘积拓扑保证其连续；逐坐标相等又保证唯一性。这证明拓扑逆极限的泛性质。

同时记录一个后面使用的柱集事实。由相容关系，对 $0\le i\le N$ 有 $p_i=f^{N-i}p_N$。因而，对开集 $O_0,\ldots,O_N\subseteq X$，
$$
\bigcap_{i=0}^N p_i^{-1}(O_i)=p_N^{-1}(W),\qquad W=\bigcap_{i=0}^N(f^{N-i})^{-1}(O_i).
$$
$W$ 开；左侧非空时 $W$ 非空。任意非空开子集均包含这样的非空柱集。

现在取 $(Y,S,g)$。对每个 $j\ge0$，由 $gS=fg$ 得
$$
f\bigl(g(S^{-j-1}y)\bigr)=g(S^{-j}y),
$$
故所给 $\widetilde g$ 落在 $\mathcal L_f$，且由各坐标连续而连续。首坐标给 $P_f\widetilde g=g$；比较首坐标及所有其余坐标，得到 $\widetilde gS=U_f\widetilde g$。

若 $h:Y\to\mathcal L_f$ 也满足这两式，则 $S,U_f$ 可逆使 $hS^{-j}=U_f^{-j}h$，所以
$$
p_jh(y)=P_fU_f^{-j}h(y)=P_fh(S^{-j}y)=g(S^{-j}y).
$$
全部坐标被强制为 $\widetilde g$ 的坐标，故 $h=\widetilde g$。

再设 $g$ 满射。给定 $\ell=(x_j)_{j\ge0}\in\mathcal L_f$，令
$$
B_N=\{y\in Y:g(S^{-j}y)=x_j\text{ 对所有 }0\le j\le N\}.
$$
这些是递减闭集。选取 $z\in Y$ 使 $g(z)=x_N$，置 $y=S^Nz$；则对 $0\le j\le N$，
$$
g(S^{-j}y)=g(S^{N-j}z)=f^{N-j}(x_N)=x_j.
$$
所以 $B_N$ 非空。$Y$ 的紧性给出 $y\in\bigcap_NB_N$，而此时 $\widetilde g(y)=\ell$，证明提升满射。

最后，两个满足所述终对象性质的三元组之间各有唯一箭头。两个复合都是相应终对象的自箭头，故由唯一性等于恒等。两箭头因而互为连续逆映射，并保持底投影与演化。这证明唯一的动力学同胚。证毕。

**命题 17.2（直接支持组一：全部历史纤维、边界与相位拆分）。** 在定义17.0的 Zeckendorf 系统中，对 $x\in K\setminus D$，其唯一前驱仍在 $K\setminus D$，记为 $r(x)$，并定义
$$
\lambda(x)=(r^j(x))_{j\ge0}.
$$
对 $\varepsilon\in\{u,v\}$ 定义双向状态序列及完整历史
$$
c_n^\varepsilon=Z(n)\quad(n\ge0),\qquad c_{-m}^\varepsilon=r^{m-1}(\varepsilon)\quad(m\ge1),\qquad \ell_k^\varepsilon=(c_{k-j}^\varepsilon)_{j\ge0}\quad(k\in\mathbb Z).
$$
这些对象均有定义，并满足
$$
Tc_k^\varepsilon=c_{k+1}^\varepsilon,\qquad U\ell_k^\varepsilon=\ell_{k+1}^\varepsilon,\qquad P\ell_k^\varepsilon=c_k^\varepsilon,\qquad Q\ell_k^\varepsilon=[k\phi].
$$

$P$ 的全部纤维准确为
$$
P^{-1}(\{Z(n)\})=\{\ell_n^u,\ell_n^v\}\quad(n\ge0),\qquad P^{-1}(\{x\})=\{\lambda(x)\}\quad(x\notin D).
$$
对于 $n\ge0$，这两个历史的第 $0,\ldots,n$ 个坐标相同，准确等于 $Z(n),Z(n-1),\ldots,Z(0)$，首次区别在第 $n+1$ 个坐标：
$$
p_{n+1}(\ell_n^u)=u,\qquad p_{n+1}(\ell_n^v)=v.
$$
特别地，零状态有且仅有两条历史
$$
\ell_0^u=(0,u,r(u),r^2(u),\ldots),\qquad \ell_0^v=(0,v,r(v),r^2(v),\ldots).
$$
两个交替状态 $u,v$ 自身却各只有一条完整历史。

原相位映射与历史相位映射的纤维区别准确如下。对每个 $m\ge1$，
$$
H^{-1}(\{[-m\phi]\})=\{c_{-m}^u,c_{-m}^v\},\qquad P^{-1}(\{c_{-m}^\varepsilon\})=\{\ell_{-m}^\varepsilon\}.
$$
$Q$ 连续满射，其二点纤维恰位于整个整数轨道 $\mathcal O$，具体为
$$
Q^{-1}(\{[k\phi]\})=\{\ell_k^u,\ell_k^v\}\qquad(k\in\mathbb Z).
$$
若 $\theta\notin\mathcal O$，以 $x_\theta$ 表示其唯一的 $H$ 原像，则
$$
Q^{-1}(\{\theta\})=\{\lambda(x_\theta)\}.
$$
因此，负轨道 $E_-$ 上原有的两个当前状态各自只提升为一条历史；非负轨道 $E_+$ 上原有的唯一当前状态提升为两条历史；其余相位保持单点。新出现的二点相位准确是 $E_+$，没有四点纤维。

此外，对任意 $\ell\in L$ 及 $k\in\mathbb Z$，
$$
H(P(U^k\ell))=Q(\ell)+[k\phi].
$$
所以即使保留全部双向相位读数，仍然只有 $Q$ 的区分能力：
$$
\bigl(H(P(U^k\ell))\bigr)_{k\in\mathbb Z}=\bigl(H(P(U^k\ell'))\bigr)_{k\in\mathbb Z}\quad\Longleftrightarrow\quad Q(\ell)=Q(\ell').
$$
本条使用的单步分支与原相位纤维分别是[前置卷定理375.2及372.4](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)；完整历史纤维由以下证明确定。

**证明。** 因 $D$ 中每一点仅有有限个非零数字，而 $u,v$ 各有无限多个非零数字，所以 $u,v\notin D$。若 $x\notin D$，则 $x\ne0$，故有唯一前驱 $y$。假如 $y=Z(n)$，则 $x=Ty=Z(n+1)\in D$，矛盾。因此 $r:K\setminus D\to K\setminus D$ 有定义，所有迭代 $r^j(x)$ 都有定义。

若 $\ell=(x_j)_{j\ge0}\in P^{-1}(\{x\})$ 且 $x\notin D$，则每个 $x_j$ 都不在 $D$：否则 $x_j=Z(a)$ 会给出 $x=T^jZ(a)=Z(a+j)\in D$。所以逐次前驱都唯一，强制 $x_j=r^j(x)$。反之，$T(r^{j+1}(x))=r^j(x)$ 保证 $\lambda(x)\in L$。这证明全部非核心状态的单点历史纤维，包括 $u,v$。

由 $TZ(n)=Z(n+1)$ 及 $Z$ 单射，对 $a\ge1$，状态 $Z(a)$ 非零，而 $Z(a-1)$ 已是其前驱，故它是唯一前驱。因此任取 $\ell\in P^{-1}(\{Z(n)\})$，其前 $n+1$ 个坐标被强制为
$$
Z(n),Z(n-1),\ldots,Z(0).
$$
随后唯一可能的选择为 $u$ 或 $v$。选定其一后，该点属于 $K\setminus D$，由上一段，全部更早历史唯一。这既排除后续分支，也排除其他完整历史，故恰有两条，且首次差别准确位于第 $n+1$ 个坐标。这里 $n=0$ 无须另加假设，直接给出显示的两条零历史。

由 $Tr(x)=x$、$Tu=Tv=0$ 及有限核心后继式，分 $k\le-2$、$k=-1$、$k\ge0$ 三种情形得到 $Tc_k^\varepsilon=c_{k+1}^\varepsilon$。这保证每个 $\ell_k^\varepsilon$ 属于 $L$，并逐坐标给出 $U\ell_k^\varepsilon=\ell_{k+1}^\varepsilon$ 与 $P\ell_k^\varepsilon=c_k^\varepsilon$。

对 $m\ge1$，有
$$
T^{m-1}c_{-m}^u=u,\qquad T^{m-1}c_{-m}^v=v.
$$
因此 $c_{-m}^u\ne c_{-m}^v$。它们都属于 $K\setminus D$，各自的唯一历史为 $\ell_{-m}^u$、$\ell_{-m}^v$。又由 $T^mc_{-m}^\varepsilon=0$ 和相位交换式，
$$
H(c_{-m}^\varepsilon)+[m\phi]=H(0)=0,
$$
故它们均位于相位 $[-m\phi]$ 的纤维。该纤维按前置恰有两点，所以所列两点就是其全部原像。这也验证了负一时刻的边界为 $\{u,v\}$，而零时刻的当前状态已合为 $\{0\}$。

$Q=HP$ 连续满射，且 $QU=R Q$，其中 $R(\theta)=\theta+[\phi]$。因为 $U,R$ 都可逆，将该式与逆映射复合，得到 $QU^{-1}=R^{-1}Q$，继而对所有整数 $k$ 有 $QU^k=R^kQ$。在上述轨道上，这给出 $Q\ell_k^\varepsilon=[k\phi]$。对 $k\ge0$，两条历史在第 $k+1$ 个坐标不同；对 $k<0$，它们已在第零个坐标不同。因此所有显示的二点集合确实各含两个不同元素。

现在穷尽全部相位。若 $\theta=[n\phi]\in E_+$，则 $H^{-1}(\{\theta\})=\{Z(n)\}$，其 $P$ 纤维恰有上述两条历史。若 $\theta=[-m\phi]\in E_-$，则 $H$ 纤维恰为 $c_{-m}^u,c_{-m}^v$，而这两个状态的 $P$ 纤维各为单点。若 $\theta\notin\mathcal O$，则 $\theta\notin E_-$，所以 $H$ 纤维只有一点 $x_\theta$；该点不能属于 $D$，否则其相位属于 $E_+$。因此其 $P$ 纤维同样只有一点。三种情形互斥且穷尽圆周，证明完整分类，并说明为何不能把两个二点纤维数目相乘得到四点。

最后，$QU^k=R^kQ$ 就是所有双向相位读数的显示公式。相位 $Q(\ell)$ 相等时，全部读数相等；全部读数相等时，取 $k=0$ 即得 $Q(\ell)=Q(\ell')$。证毕。

**命题 17.3（直接支持组二：极小性与连续选史的准确障碍）。** 本模型的 $(K,T)$ 与 $(L,U)$ 均为极小系统，此处极小指每一点的非负时间轨道稠密。特别地，对任取 $\ell_0\in P^{-1}(\{0\})$，
$$
\overline{\{U^n\ell_0:n\ge0\}}=L.
$$
集合 $Q^{-1}(\mathcal O)$ 准确分解为两条互不相交的稠密整数轨道
$$
\{\ell_k^u:k\in\mathbb Z\},\qquad \{\ell_k^v:k\in\mathbb Z\}.
$$

集合意义的截面 $s:K\to L$、$Ps=\operatorname{id}_K$ 存在，但每一个这样的截面的连续点集都准确等于 $K\setminus D$。因此 $P$ 没有连续全局截面。更强地，对任何非空开集 $V\subseteq K$，不存在连续映射 $s:V\to L$ 使 $P(s(x))=x$ 对所有 $x\in V$ 成立。即使不要求连续，也不存在满足
$$
Ps=\operatorname{id}_K,\qquad sT=Us
$$
的全局截面。

极小性所需的稠密核心、单点相位纤维及相位交换式，均取自[前置卷定理371.2、372.4、375.3](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)，不额外假设极小性。

**证明。** 先建立原系统的极小性。$H$ 连续满射且 $D$ 稠密，所以 $H(D)=\{[n\phi]:n\ge0\}$ 在圆周稠密：任一非空圆周开集的 $H$ 原像是非空开集，必与 $D$ 相交。圆周平移是同胚，故任意相位 $\theta$ 的非负旋转轨道
$$
\{\theta+[n\phi]:n\ge0\}
$$
也稠密。

任取 $x\in K$，令
$$
A=\overline{\{T^nx:n\ge0\}}.
$$
$A$ 紧，因而 $H(A)$ 在圆周闭；相位交换式使 $H(A)$ 包含稠密集合 $\{H(x)+[n\phi]:n\ge0\}$，所以 $H(A)=\mathbb T$。对于每个 $a\ge0$，存在 $y\in A$ 使 $H(y)=[a\phi]$；这个相位的唯一原像是 $Z(a)$，故 $Z(a)\in A$。因此 $D\subseteq A$，再由 $D$ 稠密得 $A=K$。这证明每个原状态的非负轨道稠密。

再取任意 $\ell\in L$ 及非空开集 $B\subseteq L$。由定理17.1的柱集等式，$B$ 包含某个非空柱集 $p_N^{-1}(W)$，其中 $W\subseteq K$ 非空且开。置 $x=P\ell$。刚证的原系统极小性给出 $m\ge0$ 使 $T^mx\in W$。由移位公式，
$$
p_N(U^{N+m}\ell)=T^m(P\ell)=T^mx\in W.
$$
于是 $U^{N+m}\ell\in B$，证明 $(L,U)$ 极小。若 $P\ell=0$，同一柱集论证只需使用 $T^m0=Z(m)$ 及 $D$ 稠密，亦直接证明题设两条零历史各自的非负轨道稠密。

命题17.2给出 $U\ell_k^\varepsilon=\ell_{k+1}^\varepsilon$，所以两组显示的点各是一条整数轨道，且各包含一条已证稠密的非负轨道。若两组中的点相等，则其相位相等，$\phi$ 无理迫使两个整数指标相同；随后与命题17.2中同一指标的两条历史不同相矛盾。因此两轨道不交；它们穷尽 $Q^{-1}(\mathcal O)$，亦由该命题的相位纤维分类得到。

接着证明截面断言。令每个 $Z(n)$ 选择 $\ell_n^u$，每个 $x\notin D$ 选择唯一的 $\lambda(x)$，便定义了集合截面，故这里不是集合选取的存在障碍。

设 $s$ 为任意集合截面，$x\notin D$。此时 $P^{-1}(\{x\})=\{s(x)\}$。若 $O\subseteq L$ 是包含 $s(x)$ 的开集，则 $P(L\setminus O)$ 闭且不含 $x$。因而
$$
W=K\setminus P(L\setminus O)
$$
是 $x$ 的开邻域。对每个 $y\in W$，其全部 $P$ 原像均在 $O$ 中，特别 $s(y)\in O$。所以 $s$ 在 $x$ 连续。这一论证不要求 $s$ 在其他点连续。

现在固定 $n\ge0$。对 $\varepsilon\in\{u,v\}$ 及 $a\ge1$，令 $\varepsilon^{(a)}$ 为 $\varepsilon$ 的前 $a$ 位截断后补零。它仍是合法有限表示，故
$$
\varepsilon^{(a)}=Z(A_a^\varepsilon),\qquad A_a^\varepsilon=\sum_{i<a}G_i\varepsilon_i,
$$
并且 $\varepsilon^{(a)}\to\varepsilon$。令
$$
y_a^\varepsilon=T^{n+1}\varepsilon^{(a)}=Z(A_a^\varepsilon+n+1).
$$
由 $T$ 连续及 $T\varepsilon=0$，两列满足
$$
y_a^u\longrightarrow Z(n),\qquad y_a^v\longrightarrow Z(n).
$$
然而，命题17.2中有限核心历史的强制前缀表明：无论截面在这两个状态上选择哪条历史，都有
$$
p_{n+1}(s(y_a^\varepsilon))=Z(A_a^\varepsilon)=\varepsilon^{(a)}.
$$
若 $s$ 在 $Z(n)$ 连续，则连续坐标映射 $p_{n+1}$ 与它复合后，在两列上必须趋于同一个值 $p_{n+1}(s(Z(n)))$。第一列却趋于 $u$，第二列趋于 $v$；$K$ 为 Hausdorff 且 $u\ne v$，矛盾。因此每个集合截面在每个 $Z(n)$ 都不连续。结合上一段，其连续点集恰为 $K\setminus D$。

同样的两列也排除局部连续截面：若截面只定义在含 $Z(n)$ 的开邻域内，两列最终仍位于其定义域，矛盾不变。任意非空开集与稠密集 $D$ 相交，故任何非空开集上都不存在连续截面。

最后，假设某个集合截面还满足 $sT=Us$。由 $Tu=Tv=0$，
$$
Us(u)=s(0)=Us(v).
$$
$U$ 单射推出 $s(u)=s(v)$，再应用 $P$ 得 $u=v$，矛盾。因此不存在这样的动力学截面，即使舍弃连续性也不例外。

综上，$P$ 以连续满射保留当前状态，$L$ 以全部相容过去提供可逆演化，但把每个当前状态连续地选成一条完整历史不可行；两条零历史各有稠密正向轨道并不改变这一截面障碍。证毕。

## 追加锚（本行以下为增补区）
## 18. 增补·加法闭图的结合律与最细确定观察商

**定义 18.0（关系复合、确定观察与因子化次序）。** 沿用定义16.0、16.3中的数字载体 $K$、有限核心 $Z$、零点 $0_K$、相位映射 $H:K\to\mathbb T$、加法闭图 $\Gamma$ 及分裂纤维的定向标记 $z_\theta^s$。特别，
$$
\mathbb T=\mathbb R/\mathbb Z,\qquad
\Gamma=\overline{\{(Z(n),Z(m),Z(n+m)):n,m\in\mathbb N\}}^{K^3}.
$$
记
$$
E_m=[-m\phi]\quad(m\ge1),\qquad E=\{E_m:m\ge1\},\qquad \Sigma=\{-1,+1\}.
$$
若 $H(x)\notin E$，置 $\mathcal S(x)=\Sigma$；若 $x=z_\theta^s$ 且 $\theta\in E$，置 $\mathcal S(x)=\{s\}$。[^rro18_phase][^rro18_fibers]

对 $A,B\subseteq K$，定义
$$
\Gamma(A,B)=\bigcup_{a\in A,\,b\in B}\Gamma(a,b).
$$
其中 $\Gamma(A,y)$、$\Gamma(x,B)$ 分别表示 $\Gamma(A,\{y\})$、$\Gamma(\{x\},B)$。再定义
$$
C(x)=\Gamma(0_K,x),\qquad C(A)=\bigcup_{x\in A}C(x),\qquad
\Lambda(x,y)=H^{-1}(\{H(x)+H(y)\}),
$$
并以 $\Lambda$ 同时表示由这些输入纤维组成的三元关系。严格左单位是满足 $\Gamma(e,x)=\{x\}$ 对所有 $x\in K$ 成立的点 $e$；严格右单位作对称定义。弱左单位只要求 $x\in\Gamma(e,x)$。

称连续满射 $q:K\to Q$ 为一个连续确定观察，若 $Q$ 是 Hausdorff 空间，且存在全函数 $D:Q^2\to Q$，满足
$$
\forall x,y\in K\ \forall z\in\Gamma(x,y),\qquad
D(q(x),q(y))=q(z).
$$
此定义不预设 $D$ 连续、结合、交换或具有单位。对两个连续满射观察，记 $q_1\succeq q_2$，若存在连续映射 $r:Q_1\to Q_2$ 使 $q_2=r\circ q_1$；此时 $r$ 自动满射，称 $q_1$ 比 $q_2$ 精细。

单值选择则是函数 $A:K^2\to K$，满足 $A(x,y)\in\Gamma(x,y)$，只要求选中一个输出，而不是将全部输出观察为同一点。另一个载体 $L$ 连同投影 $P:L\to K$ 属于状态提升的数据，其映射方向与观察商 $q:K\to Q$ 不同；以下结论不以这种提升为前提。

**假设 18.1（相位前置与明确采用的闭图分类）。** 采用如下前提。$K$ 是紧致 Hausdorff 空间，$Z[\mathbb N]$ 在其中稠密，$H$ 连续满射且满足 $H(Z(n))=[n\phi]$。相位 $\theta\notin E$ 的纤维恰有一点，相位 $\theta\in E$ 的纤维恰为两个不同的点 $z_\theta^{+1},z_\theta^{-1}$，并且
$$
H^{-1}(\{0\})=\{0_K\},\qquad
z_{E_1}^{+1}=u=(10)^\omega,\qquad z_{E_1}^{-1}=v=(01)^\omega,
$$
$$
z_{E_2}^{+1}=0v,\qquad z_{E_2}^{-1}=10v.
$$
这里 $0v,10v$ 仍按低位到高位连接。上述相位与定向约定采用定理371.2、372.2—372.4及定义16.3。[^rro18_phase][^rro18_fibers]

本节把定理16.4的完整输入纤维分类作为明确的数学前提。用定义18.0的符号，其等价写法是：令 $\theta=H(x)+H(y)$，当 $\theta\notin E$ 时，
$$
\Gamma(x,y)=H^{-1}(\{\theta\});
$$
当 $\theta\in E$ 时，
$$
\Gamma(x,y)=\{z_\theta^s:s\in\mathcal S(x)\cup\mathcal S(y)\}.
$$
这个写法与原分类一致，因为两个非空集合 $\mathcal S(x),\mathcal S(y)$ 的并恰为单点 $\{s\}$，当且仅当它们都等于 $\{s\}$；其余情形的并均为 $\Sigma$。以下命题及定理均在本假设下成立。[^rro18_fibers]

**命题 18.2（集合值结合律与全部点单位的排除）。** $\Gamma$ 非空值且交换，并且对任意 $x,y,z\in K$，
$$
\bigcup_{w\in\Gamma(x,y)}\Gamma(w,z)
=
\bigcup_{w\in\Gamma(y,z)}\Gamma(x,w).
$$
更准确地，令
$$
\sigma=H(x)+H(y)+H(z),\qquad
U=\mathcal S(x)\cup\mathcal S(y)\cup\mathcal S(z).
$$
若 $\sigma\notin E$，两边都等于单点纤维 $H^{-1}(\{\sigma\})$；若 $\sigma\in E$，两边都等于
$$
\{z_\sigma^s:s\in U\}.
$$
因此，最终相位分裂时，恰在三个输入全为同号分裂点时只保留该号，其余情形保留两个号。$0_K$ 是唯一弱左单位，也因交换性成为唯一弱右单位；但是 $K$ 中不存在严格左单位或严格右单位。[^rro18_fibers]

**证明。** 首先，
$$
E_m+E_n=E_{m+n}\in E\qquad(m,n\ge1),
$$
所以 $E$ 对相位加法封闭。这并不使其补集封闭，也不阻止与补集相加后离开 $E$。例如 $[-\phi/2]\notin E$，但它与自身之和为 $E_1$；又有 $E_1+[\phi]=0\notin E$。第一个非归属断言若不成立，便有 $(2m-1)\phi\in2\mathbb Z$，与 $\phi$ 无理矛盾；零不属于 $E$ 也由无理性得到。

假设18.1立即给出每个 $\Gamma(x,y)$ 非空，而且二元分类对 $x,y$ 对称，所以 $\Gamma$ 交换。关键是对所有输入均成立的符号传播等式
$$
\bigcup_{w\in\Gamma(x,y)}\mathcal S(w)
=
\mathcal S(x)\cup\mathcal S(y).
$$
为完整证明此式，分两种情况。若 $H(x)+H(y)\in E$，分类给出的输出恰为右侧所列符号对应的分裂点，而每个这种输出的符号集合是相应单点，取并即得等式。若 $H(x)+H(y)\notin E$，输出是非分裂相位的唯一点，故左侧为 $\Sigma$。此时 $H(x),H(y)$ 不可能都属于 $E$，否则由 $E+E\subseteq E$ 得到矛盾。因此至少一个输入的符号集合为 $\Sigma$，右侧也为 $\Sigma$。两种情况穷尽了所有中间相位，包括由非分裂输入进入 $E$ 及由混合输入离开 $E$ 的情况。

现在比较两个括号方式。每个 $w\in\Gamma(x,y)$ 均满足 $H(w)=H(x)+H(y)$，每个 $w\in\Gamma(y,z)$ 均满足 $H(w)=H(y)+H(z)$。若 $\sigma\notin E$，两边的每个末次运算都给同一个单点纤维 $H^{-1}(\{\sigma\})$；中间纤维非空，所以两边的并都恰为此纤维。

若 $\sigma\in E$，左边按末次运算的分类等于
$$
\left\{z_\sigma^s:
 s\in\left(\bigcup_{w\in\Gamma(x,y)}\mathcal S(w)\right)\cup\mathcal S(z)
\right\}
=
\{z_\sigma^s:s\in U\}.
$$
右边同样等于
$$
\left\{z_\sigma^s:
 s\in\mathcal S(x)\cup\left(\bigcup_{w\in\Gamma(y,z)}\mathcal S(w)\right)
\right\}
=
\{z_\sigma^s:s\in U\}.
$$
这里对两个中间和分别应用了已经覆盖 $E$ 内外全部情况的传播等式，没有要求二者具有相同的归属类型。这证明结合律及完整三输入分类。由于 $U$ 为单点当且仅当三个输入符号集合是同一个单点，关于唯一分支的断言也成立。

最后，$H(0_K)=0\notin E$，故 $\mathcal S(0_K)=\Sigma$。分类使 $x\in\Gamma(0_K,x)$ 对每个 $x$ 成立，所以 $0_K$ 是弱左单位。反之，若 $e$ 是弱左单位，将 $x=0_K$ 代入，得到 $0_K\in\Gamma(e,0_K)$。相位等式迫使 $H(e)=0$，再由零相位的单点纤维得到 $e=0_K$。然而
$$
\Gamma(0_K,u)=\{u,v\}\ne\{u\}.
$$
因此这个唯一可能的严格左单位并不严格，严格左单位不存在；交换性给出全部右单位结论。证毕。

**命题 18.3（零相位作用、纤维饱和与单值选择的区别）。** 对任意 $x,y\in K$，
$$
C(x)=H^{-1}(\{H(x)\}),\qquad C(C(x))=C(x),
$$
并且
$$
\Lambda(x,y)
=C(\Gamma(x,y))
=\Gamma(C(x),y)
=\Gamma(x,C(y))
=\Gamma(C(x),C(y)).
$$
原关系并不已经饱和：
$$
\Gamma(u,u)=\{0v\},\qquad
\Lambda(u,u)=\{0v,10v\},\qquad
\Gamma\subsetneq\Lambda.
$$
存在全域单值选择 $A:K^2\to K$，但不存在联合连续的这种选择。[^rro18_fibers][^rro18_phase]

**证明。** 由于 $\mathcal S(0_K)=\Sigma$，假设18.1在分裂相位处给出全部两个输出，在非分裂相位处给出唯一输出。因此 $C(x)$ 恰为 $H(x)$ 的整个纤维。该纤维非空，且其中每个 $w$ 都满足 $C(w)=C(x)$，所以
$$
C(C(x))=\bigcup_{w\in C(x)}C(w)=C(x).
$$
对任意集合 $A\subseteq K$ 再取并，也得到 $C(C(A))=C(A)$，包括空集情形。

固定 $x,y$，令 $\theta=H(x)+H(y)$。每个 $w\in\Gamma(x,y)$ 都满足 $C(w)=H^{-1}(\{\theta\})$，而 $\Gamma(x,y)$ 非空，故
$$
C(\Gamma(x,y))=H^{-1}(\{\theta\})=\Lambda(x,y).
$$
命题18.2的结合律给出
$$
\Gamma(C(x),y)
=\Gamma(\Gamma(0_K,x),y)
=\Gamma(0_K,\Gamma(x,y))
=C(\Gamma(x,y)).
$$
交换性同样给出 $\Gamma(x,C(y))=\Lambda(x,y)$。最后，对每个 $y'\in C(y)$，有 $H(y')=H(y)$，于是
$$
\Gamma(C(x),C(y))
=\bigcup_{y'\in C(y)}\Gamma(C(x),y')
=\bigcup_{y'\in C(y)}\Lambda(x,y')
=\Lambda(x,y).
$$
最后一个并取在非空集合上，且每项是同一纤维。

由 $H(u)=E_1$、$\mathcal S(u)=\{+1\}$、$E_1+E_1=E_2$，分类给出 $\Gamma(u,u)=\{z_{E_2}^{+1}\}=\{0v\}$。但 $E_2$ 的整个纤维是 $\{0v,10v\}$，且这两个字不同。因此严格包含成立，不能把 $\Gamma$ 本身替换为饱和关系。

逐点单值选择可以明确规定：输出相位不在 $E$ 时取唯一输出；输出相位在 $E$ 且正号被允许时取正号输出，否则取负号输出。分类保证每个输入对都恰落入一个这样的规定，且选中的点属于 $\Gamma(x,y)$。

假设存在联合连续的单值选择 $A$。自然相位不属于 $E$，因为 $[n\phi]=[-m\phi]$、$n\ge0,m\ge1$ 将迫使 $(n+m)\phi\in\mathbb Z$。因此分类与 $H(Z(n))=[n\phi]$ 给出
$$
\Gamma(Z(n),Z(m))=\{Z(n+m)\},\qquad
A(Z(n),Z(m))=Z(n+m).
$$
$A$ 的图在 $K^3$ 中闭：它是连续映射 $(x,y,z)\mapsto(A(x,y),z)$ 下的闭对角线的原像。这个闭图包含全部自然加法三元组，所以也包含其闭包 $\Gamma$。但 $\Gamma$ 同时包含 $(0_K,u,u)$ 和 $(0_K,u,v)$，与函数在输入 $(0_K,u)$ 处只能有一个值矛盾。这证明连续选择不存在；逐点选择的存在既不提供这种连续性，也没有断言该选择满足结合律或单位律。证毕。

**定理 18.4（最细连续确定观察与全部允许的后处理）。** 给定连续满射 $q:K\to Q$，其中 $Q$ 是 Hausdorff 空间。以下条件等价。[^rro18_fibers][^rro18_quotient]

（甲）存在全函数 $D:Q^2\to Q$，使
$$
\forall x,y\in K\ \forall z\in\Gamma(x,y),\qquad
D(q(x),q(y))=q(z).
$$

（乙）存在连续满射 $p:\mathbb T\to Q$，使 $q=p\circ H$，并且其相等关系核是加法同余，即对所有 $a,a',b,b'\in\mathbb T$，
$$
p(a)=p(a'),\ p(b)=p(b')
\quad\Longrightarrow\quad
p(a+b)=p(a'+b').
$$

（丙）存在闭子群 $N\le\mathbb T$ 及同胚 $h:\mathbb T/N\to Q$，使
$$
q=h\circ\pi_N\circ H,
$$
其中 $\mathbb T/N$ 取商拓扑，$\pi_N(a)=a+N$。这里 $h$ 是空间同胚，不预设 $Q$ 上已有任何群运算。

这些条件成立时，$p,N,h,D$ 均由给定的 $q$ 唯一确定，而且
$$
N=p^{-1}(\{p(0)\}),\qquad
p(a)=p(b)\ \Longleftrightarrow\ a-b\in N,
$$
$$
D(p(a),p(b))=p(a+b),\qquad
e_Q=p(0)=q(0_K),\qquad
\iota_Q(p(a))=p(-a).
$$
$D$ 与 $\iota_Q$ 自动连续；它们使 $Q$ 成为紧致交换拓扑群，$p$ 成为满射连续群同态。因此 $H$ 是因子化次序中最精细的连续确定观察。

更具体地，允许的连续满射后处理 $p:\mathbb T\to Q$ 恰是满足乙中同余条件的那些映射，等价地，其纤维恰为某个闭子群的陪集。对任意闭子群 $N$，$q_N=\pi_N\circ H$ 都给出这种观察，并且
$$
q_{N_1}\succeq q_{N_2}
\quad\Longleftrightarrow\quad N_1\subseteq N_2.
$$
并非每个连续满射后处理都允许确定运算；例如 $p([t])=\cos(2\pi t)$ 不允许。最后，$\Gamma$ 与 $\Lambda$ 具有完全相同的连续确定观察，尽管两关系严格不同。

**证明。** 先证甲推出乙。命题18.3给出 $C(x)=H^{-1}(\{H(x)\})$，特别 $x\in C(x)$。对任何 $z\in C(x)=\Gamma(0_K,x)$，甲分别应用于输出 $x$ 和 $z$，得到
$$
q(z)=D(q(0_K),q(x))=q(x).
$$
因此 $q$ 在每个 $H$ 纤维上恒定。$H$ 满射，所以存在唯一的满射函数 $p:\mathbb T\to Q$，满足 $q=p\circ H$。

这个因子映射连续，而不是额外假设连续。事实上，$H$ 是从紧致空间到 Hausdorff 空间的连续满射，所以是闭映射：每个闭集在 $K$ 中紧，其像在 $\mathbb T$ 中紧而闭。闭满射是商映射，因为若 $H^{-1}(V)$ 开，则
$$
\mathbb T\setminus V=H(K\setminus H^{-1}(V))
$$
闭，故 $V$ 开。于是对每个开集 $O\subseteq Q$，由
$$
H^{-1}(p^{-1}(O))=q^{-1}(O)
$$
开，得到 $p^{-1}(O)$ 开。

任取 $a,b\in\mathbb T$，利用 $H$ 满射选择 $x,y$ 使 $H(x)=a,H(y)=b$，再利用非空值性选择 $z\in\Gamma(x,y)$。甲和相位等式给出
$$
D(p(a),p(b))=q(z)=p(a+b).
$$
因此若 $p(a)=p(a')$ 且 $p(b)=p(b')$，同一个 $D$ 值同时等于 $p(a+b)$ 和 $p(a'+b')$，得到乙的同余条件。$p$ 满射又说明这条公式已经唯一确定 $D$。

反过来，若乙成立，规定 $D(p(a),p(b))=p(a+b)$。同余条件保证更换任一代表均不改变结果，满射性保证在 $Q^2$ 上处处有定义。对任意 $z\in\Gamma(x,y)$，有 $H(z)=H(x)+H(y)$，所以
$$
D(q(x),q(y))=p(H(x)+H(y))=p(H(z))=q(z).
$$
这证明乙推出甲。

接着证明闭子群描述。乙中的双槽同余条件等价于所有平移都保持相等关系核：
$$
p(a)=p(b)\quad\Longrightarrow\quad
p(a+t)=p(b+t)\qquad(t\in\mathbb T).
$$
双槽条件取相同的第二槽即得平移条件；反向先以平移条件替换第一槽，再利用加法交换性替换第二槽，即得双槽条件。

置 $N=p^{-1}(\{p(0)\})$。$Q$ Hausdorff，使单点 $\{p(0)\}$ 闭，故 $N$ 闭。显然 $0\in N$。若 $n,m\in N$，同余条件给出 $p(n+m)=p(0+0)=p(0)$，所以 $n+m\in N$。若 $n\in N$，将 $p(n)=p(0)$ 平移 $-n$，得到 $p(0)=p(-n)$，所以 $-n\in N$。因此 $N$ 是闭子群。对任意 $a,b$，先平移 $-b$、反向再平移 $b$，得到
$$
p(a)=p(b)
\quad\Longleftrightarrow\quad
p(a-b)=p(0)
\quad\Longleftrightarrow\quad a-b\in N.
$$

所以 $h(a+N)=p(a)$ 定义良好且双射。由于 $p=h\circ\pi_N$ 且 $\pi_N$ 是商映射，$h$ 连续。$\mathbb T/N$ 是紧空间的连续像，故紧；连续双射 $h$ 的目标 $Q$ Hausdorff，因此 $h$ 是闭映射，其逆连续。这证明乙推出丙。反向，若丙成立，令 $p=h\circ\pi_N$。它连续满射，而 $h$ 单射保证 $p(a)=p(b)$ 当且仅当 $a-b\in N$。子群对加法封闭，故这个关系是加法同余，得到乙。$p$ 已由 $q$ 唯一确定，$N$ 由显示的零纤维公式唯一确定，$h$ 又由 $h\circ\pi_N=p$ 唯一确定。

现在证明全部群结构与连续性。$Q$ 是 $K$ 的连续像，故紧。任取 $a,b,c\in\mathbb T$，已经证明的公式给出
$$
D(D(p(a),p(b)),p(c))=p((a+b)+c)
=p(a+(b+c))=D(p(a),D(p(b),p(c))).
$$
$ p $ 满射，因此 $D$ 结合。交换性同理由 $a+b=b+a$ 得到，单位律由 $a+0=0+a=a$ 得到。若 $p(a)=p(b)$，则 $a-b\in N$，从而 $(-a)-(-b)\in N$，故 $p(-a)=p(-b)$；所以 $\iota_Q(p(a))=p(-a)$ 定义良好。两侧乘积公式均给
$$
D(p(a),\iota_Q(p(a)))=D(\iota_Q(p(a)),p(a))=p(0).
$$
因此这些数据确实构成交换群，而不是只构成一个结合的二元运算。

为证明联合连续性，考虑连续满射
$$
p\times p:\mathbb T^2\longrightarrow Q^2.
$$
其定义域紧，目标 Hausdorff，所以如前述论证一样，它是闭的商映射。圆周加法连续，且
$$
D\circ(p\times p)=p\circ +.
$$
右侧连续。对于任意开集 $O\subseteq Q$，
$$
(p\times p)^{-1}(D^{-1}(O))=(p\circ +)^{-1}(O)
$$
开，商映射性质遂给出 $D^{-1}(O)$ 开。这是 $D$ 的联合连续性证明，并未使用一般的两个商映射之积仍为商映射这一断言。取逆连续性同样由
$$
\iota_Q\circ p=p\circ(a\mapsto-a)
$$
以及 $p$ 是商映射得到。于是 $Q$ 为紧致交换拓扑群。显示的运算公式还说明 $p$ 保持运算和单位，故是连续群同态。

为确认每个闭子群确实产生所列 Hausdorff 观察，固定任意闭子群 $N\le\mathbb T$。商映射 $\pi_N$ 是开映射：对开集 $V\subseteq\mathbb T$，
$$
\pi_N^{-1}(\pi_N(V))=V+N=\bigcup_{n\in N}(V+n)
$$
开。若 $a+N\ne b+N$，则 $d=a-b\notin N$。$N$ 闭，所以存在零的开邻域 $W$，使 $(d+W)\cap N=\varnothing$。由圆周减法在 $(0,0)$ 连续，可取零的开邻域 $V$，满足 $V-V\subseteq W$。开集 $\pi_N(a+V)$ 和 $\pi_N(b+V)$ 分别包含两个陪集，且互不相交；否则存在 $v,w\in V$ 使 $d+v-w\in N$，与 $(d+W)\cap N=\varnothing$ 矛盾。因此 $\mathbb T/N$ Hausdorff。它又是紧空间的连续像，故紧。$\pi_N$ 的相等关系核为陪集同余，所以将已证的乙推出甲及连续性结论应用于 $p=\pi_N$，即得 $q_N=\pi_N\circ H$ 是连续确定观察。

$H$ 自身满足甲，只需取 $Q=\mathbb T$ 和圆周加法为 $D$。任意满足甲的 $q$ 均已证明唯一地连续因子化为 $p\circ H$，所以 $H\succeq q$；这正是所定义次序中的最精细性，而不是关于任意后处理的无条件断言。

对规范商，若 $N_1\subseteq N_2$，则
$$
r(a+N_1)=a+N_2
$$
定义良好且满射。等式 $r\circ\pi_{N_1}=\pi_{N_2}$ 与 $\pi_{N_1}$ 的商映射性质保证 $r$ 连续，并且 $q_{N_2}=r\circ q_{N_1}$。反之，若这个观察因子化成立，$H$ 满射给出 $\pi_{N_2}=r\circ\pi_{N_1}$。任取 $n\in N_1$，有
$$
\pi_{N_2}(n)=r(\pi_{N_1}(n))=r(\pi_{N_1}(0))=\pi_{N_2}(0),
$$
所以 $n\in N_2$。这证明因子化次序的闭子群包含描述。

为否定所有连续后处理都允许确定运算，取连续满射
$$
p:\mathbb T\to[-1,1],\qquad p([t])=\cos(2\pi t).
$$
令 $a=[1/4]$、$b=[-1/4]$、$t=[1/4]$，则
$$
p(a)=p(b)=p(t)=0,\qquad p(a+t)=-1,\qquad p(b+t)=1.
$$
相等关系核不被这个平移保持。等价地，任何所需运算都将同时被迫满足 $D(0,0)=-1$ 与 $D(0,0)=1$，故不存在。

最后，若 $q,D$ 对 $\Gamma$ 满足甲，前面已证 $q$ 在每个 $C$ 纤维上恒定。对 $r\in\Lambda(x,y)$，取任意 $w\in\Gamma(x,y)$；命题18.3给出 $r\in C(w)$，因而
$$
q(r)=q(w)=D(q(x),q(y)).
$$
所以同一个 $q,D$ 对 $\Lambda$ 也确定。反向由 $\Gamma\subseteq\Lambda$ 立即成立。这只说明两关系具有相同的确定观察，并不消除命题18.3中的严格关系差异。商上的单位 $q(0_K)$ 来自对 $C$ 纤维的识别，也不使 $0_K$ 成为原关系的严格单位。证毕。

[^rro18_phase]: 《CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF》，定理371.2、372.2—372.4及377.1；固定提交 c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb 的[相位前置文本](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)。其中定理372.2—372.3给出两分支的实值域及公共前缀的奇偶定向，定理372.4给出全部圆周分裂纤维。

[^rro18_fibers]: 第16节定义16.3及定理16.4：定向标记与加法闭图的完整输入纤维分类。本节在假设18.1中明确采用该分类；结合律及确定观察商的结论由命题18.2—定理18.4另行证明。

[^rro18_quotient]: Nicolas Bourbaki, *General Topology: Chapters 1–4*，第I章 Topological Structures 与第III章 Topological Groups，Springer，DOI：[10.1007/978-3-642-61701-0](https://doi.org/10.1007/978-3-642-61701-0)。本节所需的商映射下降、闭子群陪集与连续群运算论证均在定理18.4的证明中给出。

## 追加锚（本行以下为增补区）
## 19. Zeckendorf 最低位的三角阵与分别连续紧实现障碍

**定义 19.1（规范数字与最低位观察）。** 在通常 ZFC 中，取 $\mathbb N=\{0,1,\ldots\}$，并定义
$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j.
$$
数字按低位到高位排列。令
$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ 对所有 }j\in\mathbb N\},
$$
其中 $\{0,1\}$ 取离散拓扑，$K$ 取乘积子空间拓扑。以 $Z(n)$ 表示 $n$ 的有限支撑规范数字向量，并在其后补零；亦即
$$
n=\sum_{j\ge0}G_jZ(n)_j.
$$
记 $e_i$ 为仅在位置 $i$ 取一的数字向量，并置
$$
d_0(x)=x_0,\qquad f(n)=d_0(Z(n)),\qquad o=Z(0),\qquad u=(10)^\infty,\qquad v=(01)^\infty.
$$
本节的 $f$ 专指最低位观察。再定义
$$
a_k=\sum_{j=0}^{k}G_{2j},\qquad b_l=G_{2l}\qquad(k,l\in\mathbb N).
$$
空和取零。数字向量的有限和按坐标作通常整数加法。载体及规范字的记号对应《情境时空算术：Zeckendorf》第 371.1 条。([raw.githubusercontent.com](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md))

**定理 19.2（全部指标上的规范展开与严格三角公式）。** 对所有 $k,l\in\mathbb N$，有
$$
a_k=G_{2k+1}-1,\qquad G_{2l}-1=\sum_{j=0}^{l-1}G_{2j+1}.
$$
当 $k<l$ 时，准确的规范展开为
$$
Z(a_k+b_l)=\sum_{j=0}^{k}e_{2j}+e_{2l}.
$$
当 $k\ge l$ 时，准确的规范展开为
$$
Z(a_k+b_l)=e_{2k+1}+\sum_{j=0}^{l-1}e_{2j+1}.
$$
因此
$$
f(a_k+b_l)=1\quad\Longleftrightarrow\quad k<l.
$$

**证明。** 先说明检验规范性的唯一性依据。长度为 $L$ 的合法数字窗，经权值求和，恰好且不重复地表示 $0,\ldots,G_L-1$。当 $L=0$ 时只有空窗，其值为零；当 $L=1$ 时值为零或一。若 $L\ge2$，最高位为零的窗，由归纳假设恰给区间 $[0,G_{L-1}-1]$ 中的整数。最高位为一时，次高位必须为零，其余长度为 $L-2$ 的窗恰给
$$
G_{L-1}+[0,G_{L-2}-1]=[G_{L-1},G_L-1]
$$
中的整数。这两个整数区间不交，且并为全部目标区间，故存在性及唯一性同时归纳成立。由于 $G_L$ 无界，每个自然数都有有限规范展开；任意两个有限展开均可补零到同一长度，因而全局唯一。

第一个求和恒等式在 $k=0$ 时为 $1=2-1$；若它对 $k$ 成立，则
$$
a_{k+1}=G_{2k+1}-1+G_{2k+2}=G_{2k+3}-1.
$$
第二个恒等式在 $l=0$ 时为 $G_0-1=0$；由 $l$ 到 $l+1$ 的归纳步为
$$
G_{2l}-1+G_{2l+1}=G_{2l+2}-1.
$$

若 $k<l$，原来的非零位置为 $0,2,\ldots,2k$，新位置为 $2l$。它与前一非零位置的距离至少为二，所以显示的向量各位均为零或一，且没有相邻的一。其权值正是 $a_k+b_l$，唯一性使它成为规范展开，最低位为一。

若 $k\ge l$，两个恒等式给出
$$
a_k+b_l=G_{2k+1}+(G_{2l}-1)
=G_{2k+1}+\sum_{j=0}^{l-1}G_{2j+1}.
$$
当 $l\ge1$ 时，下部非零位置为 $1,3,\ldots,2l-1$，最高位置为 $2k+1$，两部分之间的距离为 $2(k-l+1)\ge2$。因此该展开合法且规范，位置零取零。当 $l=0$ 时下部为空，所得展开仅在位置 $2k+1$ 取一，仍然最低位为零。特别地，$a_k+b_0=a_k+1=G_{2k+1}$，包括 $k=l=0$ 时的 $2=G_1$。

当 $k=l$ 时，上述第二种展开准确化为
$$
Z(a_k+b_k)=\sum_{j=0}^{k}e_{2j+1},\qquad a_k+b_k=G_{2k+2}-1,
$$
所以对角线上同样为零。全部情形均已包含，三角公式成立。证毕。

**定理 19.3（紧输入与分别连续映射的双极限必要条件）。** 设 $P,Q$ 为紧拓扑空间，$W$ 为 Hausdorff 空间，$C:P\times Q\to W$ 分别连续。输入空间不要求 Hausdorff，输出空间不要求紧。给定序列 $x_k\in P$、$y_l\in Q$，假定下列所有内层及外层极限均存在：
$$
r_k=\lim_{l\to\infty}C(x_k,y_l),\qquad
s_l=\lim_{k\to\infty}C(x_k,y_l),
$$
$$
r=\lim_{k\to\infty}r_k,\qquad
s=\lim_{l\to\infty}s_l.
$$
则 $r=s$。

**证明。** 对序列 $x_k$，令
$$
F_N=\overline{\{x_k:k\ge N\}}\subseteq P.
$$
这些非空闭集递减，由紧性得 $\bigcap_NF_N\ne\varnothing$。取其中一点 $x$。为明确使用子网而非子序列，令 $D_x$ 由满足 $x_k\in U$ 的二元组 $(k,U)$ 组成，其中 $U$ 是 $x$ 的开邻域，并规定
$$
(k,U)\preceq(k',U')\quad\Longleftrightarrow\quad k\le k'\text{ 且 }U'\subseteq U.
$$
因为 $x$ 属于每个尾集的闭包，任意两个这样的二元组，都有一个指标不小于二者、邻域包含于二者交集的共同上界。因此 $D_x$ 有向。投影 $(k,U)\mapsto k$ 保序且共尾，所得子网收敛到 $x$。同理，$y_l$ 有收敛到某个 $y\in Q$ 的子网。记这两个子网为 $x_{k(\alpha)}\to x$ 与 $y_{l(\beta)}\to y$。

固定 $k$，第二变量的连续性给
$$
C(x_k,y)=\lim_\beta C(x_k,y_{l(\beta)})=r_k.
$$
最后一个等号使用原内层极限及其子网具有同一极限，并使用 $W$ 中极限的唯一性。同理，对每个固定 $l$，有
$$
C(x,y_l)=s_l.
$$
再分别沿两个已选子网取极限，得到
$$
C(x,y)=\lim_\alpha C(x_{k(\alpha)},y)
=\lim_\alpha r_{k(\alpha)}=r,
$$
$$
C(x,y)=\lim_\beta C(x,y_{l(\beta)})
=\lim_\beta s_{l(\beta)}=s.
$$
所以 $r=s$。此证明没有要求任何输入序列存在收敛子序列。证毕。

**定理 19.4（最低位加法表不存在任何分别连续紧实现）。** 不存在紧空间 $X$、集合映射 $j:\mathbb N\to X$ 及分别连续映射
$$
B:X\times X\to\{0,1\}
$$
使得
$$
B(j(n),j(m))=f(n+m)\qquad(n,m\in\mathbb N).
$$
这里不要求 $j$ 单射、连续或具有稠密像。

更一般地，设 $Y$ 为任意拓扑空间，$W$ 为 Hausdorff 空间，$w_0,w_1\in W$ 且 $w_0\ne w_1$。不存在同时满足下列条件的数据：紧空间 $X$，集合映射 $j:\mathbb N\to X$，分别连续映射 $M:X\times X\to Y$，以及连续观察 $q:Y\to W$，使
$$
q(M(j(n),j(m)))=w_{f(n+m)}\qquad(n,m\in\mathbb N).
$$
特别地，将输出改为任意紧 Hausdorff 空间，并保留取值于离散二点集或实数的连续最低位观察，仍然不能得到这样的实现。若还存在 $h:\mathbb N\to Y$，满足 $q(h(n))=w_{f(n)}$，则要求 $M(j(n),j(m))=h(n+m)$ 更不可能。

**证明。** 在较一般的情形中，$C=q\circ M$ 分别连续。取
$$
x_k=j(a_k),\qquad y_l=j(b_l).
$$
定理 19.2 给出：对每个固定 $k$，当 $l>k$ 时 $C(x_k,y_l)=w_1$；对每个固定 $l$，当 $k\ge l$ 时 $C(x_k,y_l)=w_0$。因此
$$
\lim_{k\to\infty}\lim_{l\to\infty}C(x_k,y_l)=w_1,
\qquad
\lim_{l\to\infty}\lim_{k\to\infty}C(x_k,y_l)=w_0.
$$
这与定理 19.3 矛盾。取 $Y=W=\{0,1\}$、$q$ 为恒等映射，即得第一项断言。证明只使用观察后的常值尾，不要求未观察输出在 $Y$ 中的任何迭代极限存在。证毕。

**定理 19.5（任意紧标签及保留读数的紧历史扩张）。** 设 $A$ 为任意紧标签空间，$t:\mathbb N\to A$ 为任意集合映射，并令
$$
j(n)=(Z(n),t(n)).
$$
对任何包含 $j[\mathbb N]$ 的闭子空间 $X\subseteq K\times A$，定义连续读数
$$
r=d_0\circ\operatorname{pr}_K:X\to\{0,1\}.
$$
不存在分别连续的 $\mu:X\times X\to X$ 使
$$
r(\mu(j(n),j(m)))=f(n+m)\qquad(n,m\in\mathbb N).
$$
这包括整个 $K\times A$ 以及 $j[\mathbb N]$ 的闭包，也包括要求 $\mu(j(n),j(m))=j(n+m)$ 的更强情形。

又设 $\widetilde X$ 为紧 Hausdorff 空间，$\pi:\widetilde X\to K$ 为连续满射。任取满足
$$
\pi(\widetilde j(n))=Z(n)
$$
的提升 $\widetilde j:\mathbb N\to\widetilde X$。不存在分别连续的 $\widetilde\mu:\widetilde X\times\widetilde X\to\widetilde X$，使得对全部 $n,m\in\mathbb N$ 有
$$
d_0\bigl(\pi(\widetilde\mu(\widetilde j(n),\widetilde j(m)))\bigr)=f(n+m).
$$
因而，仅要求
$$
\pi(\widetilde\mu(\widetilde j(n),\widetilde j(m)))=Z(n+m)
$$
而允许输出历史在该数字纤维内任意变化，也不能避开障碍。

**证明。** 违反无相邻一条件的数字向量构成开柱集的并，所以 $K$ 是紧 Hausdorff 乘积 $\{0,1\}^{\mathbb N}$ 的闭子空间。坐标观察 $d_0$ 连续。故 $K\times A$ 紧，闭子空间 $X$ 紧，且所定义的 $r$ 连续。将 $q=r$ 代入定理 19.4，即得标签空间上的结论。

历史扩张上，$d_0\circ\pi$ 同样连续。满射性在 ZFC 中保证可以选择所述提升，而定理 19.4 对每一种这样的选择均适用。证明不要求 $\pi$ 有连续截面，也不要求 $\widetilde\mu$ 结合、交换、有单位或可逆。证毕。

**定理 19.6（逐个固定平移不能补成全参数分别连续运算）。** 令 $T:K\to K$ 为连续后继，满足 $T(Z(n))=Z(n+1)$。对每个固定 $h\in\mathbb N$，$T^h$ 连续，并且是 $Z(n)\mapsto Z(n+h)$ 的唯一连续延拓。然而
$$
Z(b_l)\longrightarrow o,\qquad
T^{b_l}(u)=Z(b_l-1)\longrightarrow v\ne u=T^0(u).
$$
因此，逐个固定自然参数的连续平移族不能补成分别连续映射 $K\times K\to K$，使第二参数 $Z(h)$ 对应 $T^h$。连续后继的存在见《情境时空算术：Zeckendorf》第 375.2 条。([raw.githubusercontent.com](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md))

**证明。** 任意 $x\in K$ 的有限前缀补零后仍合法，故由规范唯一性，它是某个自然数的 $Z$ 像。这些截断逐坐标收敛到 $x$，所以 $Z[\mathbb N]$ 在 $K$ 中稠密。连续复合及对 $h$ 的归纳给出 $T^h$ 的连续性与核心等式；两个连续映射若在该稠密集上相同，由目标的 Hausdorff 性便处处相同。

由数字展开，$Z(a_k)\to u$，而 $a_k+1=G_{2k+1}$ 使
$$
T(Z(a_k))=Z(G_{2k+1})=e_{2k+1}\longrightarrow o.
$$
连续性给 $T(u)=o$。因此，对每个 $h\ge1$，
$$
T^h(u)=T^{h-1}(o)=Z(h-1).
$$
取 $h=b_l$，定理 19.2 的奇数位置求和式给
$$
T^{b_l}(u)=\sum_{j=0}^{l-1}e_{2j+1}\longrightarrow v.
$$
同时 $Z(b_l)=e_{2l}\to o$。

若存在所述分别连续映射 $M$，则 $M(u,Z(b_l))=T^{b_l}(u)$，而 $M(u,o)=T^0(u)=u$。第二变量的连续性将迫使同一输出序列收敛到 $u$，与其极限 $v$ 不同矛盾。若只给定核心上的完整加法等式，则第一变量的连续性及稠密性已迫使每个切片 $M(\,·\,,Z(h))=T^h$，故同一矛盾仍成立。证毕。

**定理 19.7（加法图闭包的一个精确二点纤维与选择障碍）。** 定义闭关系
$$
\Gamma=\overline{\{(Z(n),Z(m),Z(n+m)):n,m\in\mathbb N\}}\subseteq K^3,
$$
以及其输出纤维
$$
\Gamma(x,y)=\{z\in K:(x,y,z)\in\Gamma\}.
$$
每个 $\Gamma(x,y)$ 均为非空紧集，并有
$$
\Gamma(Z(n),Z(m))=\{Z(n+m)\},\qquad
\Gamma(u,o)=\{u,v\}.
$$
不存在分别连续的选择 $s:K\times K\to K$ 满足 $s(x,y)\in\Gamma(x,y)$。

**证明。** $\Gamma$ 是紧 Hausdorff 空间 $K^3$ 的闭子空间，因此紧。它向前两个坐标的投影是 $K^2$ 的紧闭子集，包含稠密集 $Z[\mathbb N]\times Z[\mathbb N]$，故投影为整个 $K^2$。这给出每个纤维的非空性；纤维在 $K$ 中闭，因而紧。

取 $\phi=(1+\sqrt5)/2$、$\alpha=\phi^{-1}$，并令
$$
\theta(x)=\left[\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j\right]\in\mathbb T=\mathbb R/\mathbb Z.
$$
由《情境时空算术：Zeckendorf》第 371.2、372.4 条，$\theta$ 连续，且
$$
\theta(Z(n))=[n\phi],\qquad
\theta^{-1}(\{[n\phi]\})=\{Z(n)\}\quad(n\in\mathbb N),
$$
$$
\theta(o)=0,\qquad
\theta(u)=\theta(v)=[-\phi],\qquad
\theta^{-1}(\{[-\phi]\})=\{u,v\}.
$$
这些是同一圆周映射在自然相位及接缝相位处的准确纤维。([raw.githubusercontent.com](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md))

条件 $\theta(z)=\theta(x)+\theta(y)$ 在 $K^3$ 中定义闭集，且包含原始加法图，所以
$$
(x,y,z)\in\Gamma\quad\Longrightarrow\quad
\theta(z)=\theta(x)+\theta(y).
$$
在输入 $(Z(n),Z(m))$ 处，输出因而属于自然相位 $[(n+m)\phi]$ 的单点纤维；原始图又包含 $Z(n+m)$，故得到第一个纤维等式。

在输入 $(u,o)$ 处，相位条件给 $\Gamma(u,o)\subseteq\{u,v\}$。另一方面，
$$
a_k+b_{k+1}=a_{k+1}
$$
使原始图中的三元组 $(Z(a_k),Z(b_{k+1}),Z(a_{k+1}))$ 收敛到 $(u,o,u)$。定理 19.2 的对角展开又使
$$
(Z(a_k),Z(b_k),Z(a_k+b_k))\longrightarrow(u,o,v).
$$
因此两个输出都属于该闭包纤维，得到准确等式 $\Gamma(u,o)=\{u,v\}$。

任意选择 $s$ 都因核心纤维的单点性而满足 $s(Z(n),Z(m))=Z(n+m)$。若它分别连续，$d_0\circ s$ 就违反定理 19.4。证毕。

**定理 19.8（固定素数乘法上的同一障碍）。** 固定素数 $p$，令
$$
P_p=\{p^n:n\in\mathbb N\},\qquad f_p(p^n)=f(n).
$$
不存在紧空间 $X$、集合映射 $\iota:P_p\to X$ 及分别连续映射 $B:X\times X\to\{0,1\}$，使
$$
B(\iota(r),\iota(s))=f_p(rs)\qquad(r,s\in P_p).
$$
特别地，不存在同时具有连续读数 $d:X\to\{0,1\}$ 和分别连续乘法 $\mu:X\times X\to X$ 的紧实现，使
$$
d(\iota(p^n))=f(n),\qquad
\mu(\iota(p^n),\iota(p^m))=\iota(p^{n+m}).
$$

**证明。** 素数幂的指数唯一，故 $f_p$ 定义良好。令 $j(n)=\iota(p^n)$。恒等式
$$
p^np^m=p^{n+m}
$$
将第一项假设变为 $B(j(n),j(m))=f(n+m)$，与定理 19.4 矛盾。第二项中的 $B=d\circ\mu$ 分别连续，并满足同一等式。其显式三角见证为
$$
f_p\bigl(p^{a_k}p^{b_l}\bigr)=1\quad\Longleftrightarrow\quad k<l.
$$
指数零对应乘法单位 $p^0=1$，其读数为 $f(0)=0$，不需排除该情形。证毕。

**定义 19.9（弱殆周期函数与半拓扑紧化）。** 令 $E=\ell^\infty(\mathbb N;\mathbb C)$，赋予上确界范数，$E^*$ 为其连续线性对偶。对 $g\in E$ 定义
$$
(R_tg)(s)=g(s+t),\qquad \mathcal O(g)=\{R_tg:t\in\mathbb N\}.
$$
称 $g$ 为弱殆周期函数，若 $\mathcal O(g)$ 在弱拓扑 $\sigma(E,E^*)$ 中的闭包紧。紧 Hausdorff 半拓扑半群是具有结合运算、且该运算分别连续的紧 Hausdorff 空间。其作为 $(\mathbb N,+)$ 的半拓扑紧化时，另带一个具有稠密像的半群同态 $\eta:\mathbb N\to S$；不要求 $\eta$ 单射。弱殆周期的平移轨道定义见 Grothendieck 的命题 7；半拓扑紧化的通常范围见 Akbari Tootkaboni 的定理 2.2。([webusers.imj-prg.fr](https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/AG/AG-6.pdf)) M. Akbari Tootkaboni, *Filters and the weakly almost periodic compactification of a semitopological semigroup*, [arXiv:1302.3204v1](https://arxiv.org/pdf/1302.3204v1), p. 1（半拓扑半群定义）及 p. 3（弱殆周期定义、定理 2.1–2.2）。

**定理 19.10（最低位观察不是弱殆周期函数）。** 将 $f$ 视为 $E$ 的元素，则
$$
f\notin\operatorname{WAP}(\mathbb N,+).
$$
此外，对任意紧 Hausdorff 半拓扑半群 $S$ 及任意半群同态 $\eta:\mathbb N\to S$，不存在连续函数 $h:S\to\mathbb C$ 使 $h(\eta(n))=f(n)$。后一断言甚至不要求 $\eta$ 的像稠密。其经典双极限背景为 Grothendieck 的定理 6、命题 7，以及 Akbari Tootkaboni 的定理 2.1–2.2。([webusers.imj-prg.fr](https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/AG/AG-6.pdf)) M. Akbari Tootkaboni, *Filters and the weakly almost periodic compactification of a semitopological semigroup*, [arXiv:1302.3204v1](https://arxiv.org/pdf/1302.3204v1), p. 1（半拓扑半群定义）及 p. 3（弱殆周期定义、定理 2.1–2.2）。

**证明。** 定义线性子空间
$$
D=\{g\in E:\lim_{l\to\infty}g(b_l)\text{ 存在}\},
$$
以及有界线性泛函
$$
L_0(g)=\lim_{l\to\infty}g(b_l)\qquad(g\in D).
$$
由 $|L_0(g)|\le\|g\|_\infty$ 且常值一函数属于 $D$，有 $\|L_0\|=1$。Hahn–Banach 定理给出其连续线性延拓 $L\in E^*$。

反设 $f$ 弱殆周期。取 $g_k=R_{a_k}f$。轨道的弱闭包紧，因此 $g_k$ 有弱收敛子网 $g_{k(\alpha)}\to g\in E$。对每个固定 $l$，点值泛函 $g\mapsto g(b_l)$ 属于 $E^*$，而三角公式使 $g_{k(\alpha)}(b_l)$ 最终为零，所以
$$
g(b_l)=0\qquad(l\in\mathbb N).
$$
于是 $g\in D$ 且 $L(g)=L_0(g)=0$。但对每个固定 $k$，同一三角公式给 $\lim_lg_k(b_l)=1$，故 $L(g_k)=1$。弱收敛又要求
$$
L(g)=\lim_\alpha L(g_{k(\alpha)})=1,
$$
矛盾。这一论证只用了弱紧性的子网、点值泛函及 Hahn–Banach 延拓。

若后一断言中的 $h$ 存在，令 $C(s,t)=h(st)$。乘法分别连续且 $h$ 连续，所以 $C:S\times S\to\mathbb C$ 分别连续，并有
$$
C(\eta(n),\eta(m))=h(\eta(n+m))=f(n+m).
$$
将连续观察取为 $h$，定理 19.4 即给矛盾。证毕。

**定理 19.11（删除连续最低位观察后，紧算术实现仍可存在）。** 令 $X=\mathbb T$，定义
$$
j(n)=[n\phi],\qquad M(s,t)=s+t.
$$
则 $X$ 紧 Hausdorff，$j$ 单射，$M$ 联合连续，且
$$
M(j(n),j(m))=j(n+m).
$$
但是不存在连续函数 $q:\mathbb T\to\mathbb R$ 满足 $q(j(n))=f(n)$。

**证明。** 通常圆周是紧 Hausdorff 空间。若 $j(n)=j(m)$，则 $(n-m)\phi$ 是整数；由 $\phi$ 无理，必有 $n=m$。圆周加法保留所示核心等式，并且圆周距离满足
$$
\rho(s+t,s'+t')\le\rho(s,s')+\rho(t,t'),
$$
所以 $M$ 联合连续。若所述 $q$ 存在，则 $q\circ M$ 分别连续，且在核心上等于 $f(n+m)$，违反定理 19.4。因此，被排除的不是一切紧空间上的加法实现，而是同时保留该连续最低位观察的分别连续实现。证毕。

## 追加锚（本行以下为增补区）
## 20. Positional precision and arithmetic-time observation on the Zeckendorf compactum

**Definition 20.1 (The carrier and the two observations).** Put
$$
\phi=\frac{1+\sqrt5}{2},\qquad
\alpha=\phi^{-1},\qquad
\beta=\alpha^2=1-\alpha,\qquad r=-\alpha,
$$
$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j.
$$
Use the low-to-high digit carrier
$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ for every }j\},
$$
with its product topology, and write $Z(n)$ for the finite Zeckendorf expansion of $n$, padded by zeros. The phase maps and rotation are
$$
F(x)=\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j,\qquad
H(x)=[F(x)],\qquad R(\theta)=\theta+[\phi].
$$
The successor $T$ replaces the alternating prefix before the first occurrence $x_jx_{j+1}=00$ by zeros and sets position $j$ to one, leaving higher positions unchanged; if there is no such occurrence, it sends the sequence to $Z(0)$. Set
$$
q_L(x)=(x_0,\ldots,x_{L-1}),\qquad f(x)=x_0,\qquad
v_t(x)=(f(T^i x))_{0\le i<t}.
$$
Both $q_0$ and $v_0$ have the single value given by the empty word. Let $\mathcal Q_L$ and $\mathcal V_t$ be their partitions into nonempty fibers. For a map $g$, its equality kernel is
$$
\ker(g)=\{(x,y)\in K^2:g(x)=g(y)\}.
$$
Finally, positional deletion is the different map $\sigma:K\to K$ defined by $(\sigma x)_j=x_{j+1}$.

The carrier, phase maps and successor are those of the Zeckendorf theory volume, §§371–375; in particular, the established properties used below are compactness, density of $Z(\mathbb N)$, continuity and surjectivity of $T$, and $TZ(n)=Z(n+1)$, $HT=RH$. ([raw.githubusercontent.com](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md))

**theorem 20.2 (Exact positional cuts, including the split endpoints).** Write
$$
a=-\alpha,\qquad b=\beta,\qquad c=-\alpha^3,\qquad
I=[a,b],\qquad u=(10)^\infty,\qquad v=(01)^\infty,
$$
and
$$
e_m=[-m\phi]\quad(m\ge1),\qquad E=\{e_m:m\ge1\}.
$$
There are exactly $G_L$ admissible words of length $L$. For such a word $p$, let $C_p=q_L^{-1}(\{p\})$ and
$$
S_p=\sum_{j<L}(-1)^{j+1}\alpha^{j+2}p_j.
$$
Its real phase interval is
$$
I_p=F[C_p]=
\begin{cases}
I,&L=0,\\
S_p+r^L I,&L>0,\ p_{L-1}=0,\\
S_p+r^{L+1}I,&L>0,\ p_{L-1}=1.
\end{cases}
$$
The circle boundaries of these images are exactly
$$
B_0^{\mathrm{pos}}=\varnothing,\qquad
B_L^{\mathrm{pos}}
=\bigcup_p\partial_{\mathbb T}H[C_p]
=\{e_1,\ldots,e_{G_L}\}\quad(L\ge1).
$$
These are boundaries in the circle, not boundaries of the clopen sets $C_p$ in $K$.

Every phase outside $E$ has a singleton $H$-fiber, and each $e_m$ has exactly two lifts. Give these two lifts their negative-side and positive-side names $x_m^-,x_m^+$. At the circle seam they are
$$
x_1^-=v,\qquad x_1^+=u.
$$
For $m\ge2$, there is a unique finite word $w$ made of the blocks $0$ and $10$ such that, with digit length $d=|w|$ and $N_w=\sum_{j<d}G_jw_j$,
$$
m=G_{d+1}-N_w.
$$
For this word,
$$
(x_m^-,x_m^+)=
\begin{cases}
(w10v,w0v),&d\text{ even},\\
(w0v,w10v),&d\text{ odd}.
\end{cases}
$$
For every $L\ge1$, these two points have different $L$-digit prefixes exactly when $m\le G_L$.

For every positive-depth cylinder, its phase image has an open arc interior $J_p$, and its full atom, with the correct split endpoints, satisfies
$$
C_p=\overline{\{Z(n):H(Z(n))\in J_p\}}^{\,K}.
$$

**Proof.** The finite value map $p\mapsto\sum_{j<L}G_jp_j$ is a bijection onto the integers from zero to $G_L-1$. At lengths zero and one this is immediate. For $L\ge2$, splitting according to the highest digit gives the disjoint value ranges
$$
[0,G_{L-1}-1]\cap\mathbb Z,\qquad
[G_{L-1},G_{L-1}+G_{L-2}-1]\cap\mathbb Z.
$$
In the second range the preceding digit is forced to zero. Induction proves both exhaustiveness and uniqueness, hence the count.

The interval formula is the exact cylinder formula of §372.3. Every positive-depth interval has positive length less than one. Distinct length-$L$ prefixes, completed by a forced zero when necessary, give incomparable block prefixes. The intersection classification of §372.3 therefore makes their interval interiors disjoint. They cover $I$, so they form consecutive intervals without gaps.

For completeness, enumerate their endpoints using the full fibers of §372.2 rather than merely counting intervals. A finite block word $w$ acts on real phases by
$$
A_w(s)=S_w+r^d s.
$$
The internal double fiber at $A_w(c)$ consists of $w0v$ and $w10v$. The recurrence and its initial values give
$$
\eta_j=\phi G_j-G_{j+1}=(-1)^{j+1}\alpha^{j+2},
\qquad r^d c=-\eta_{d+1}.
$$
Consequently,
$$
[A_w(c)]=[\phi(N_w-G_{d+1})]=e_{G_{d+1}-N_w}.
$$
The empty block word gives $d=0$ and $m=2$. For $d\ge1$, block words of digit length $d$ are exactly admissible words ending in zero. Removing this final zero and applying the finite value bijection shows that their values run once through
$$
0,\ldots,G_{d-1}-1.
$$
Their indices $m$ thus run once through
$$
G_d+1,\ldots,G_{d+1}.
$$
These disjoint successive ranges exhaust the integers at least three. The cited full-fiber classification has no other nonsingleton fibers beyond these internal pairs and the seam.

An internal endpoint is precisely a phase whose two lifts belong to different cylinders: adjacent positive intervals meet there, whereas their interiors do not overlap. The two sequences $w0v,w10v$ first differ at digit $d$. Thus their prefixes of length $L$ differ exactly when $d<L$. The displayed index ranges show that the internal fibers separated at depth $L\ge1$ have exactly the indices $2,\ldots,G_L$. The remaining circle identification joins $a$ and $b$, whose unique real preimages are $u$ and $v$; they differ already at digit zero. Its index is $m=1$. Irrationality of $\phi$ makes all the $e_m$ distinct. This proves the stated cut set. At depth zero the image is the whole circle, which has empty boundary.

Before application of $A_w$, the $10$ branch has real image $[a,c]$, while the $0$ branch has image $[c,b]$. The affine map $A_w$ preserves orientation for even $d$ and reverses it for odd $d$, giving the two oriented formulas. At the seam, approaching through $b$ gives $v$, and leaving through $a$ gives $u$.

No other cylinder image can contain an interior point of $I_p$: its positive length would force an overlap of interval interiors. Hence the entire fiber above every point of $J_p$ belongs to $C_p$. Natural phases avoid $E$, since $[n\phi]=[-m\phi]$ would make $(n+m)\phi$ an integer. Therefore
$$
C_p\cap Z(\mathbb N)=\{Z(n):H(Z(n))\in J_p\}.
$$
The left-hand side is dense in $C_p$, because $C_p$ is open and closed and $Z(\mathbb N)$ is dense. This proves the closure formula.

It also proves the asserted side interpretation. Choose a depth that separates the two points above $e_m$. Sufficiently close phases on either side belong to the corresponding adjacent cylinder. A convergent subsequence of their natural lifts has phase $e_m$ and lies in that cylinder, so it can have only the indicated one of the two limits. Compactness then gives convergence of the whole sequence. Such approaching natural phases exist because the continuous surjection $H$ takes the dense core to a dense subset of the circle. The same argument at the seam uses its two adjacent cylinders. This establishes the endpoint conventions on all of $K$. $\square$

Attached reference: the cylinder and double-fiber inputs are precisely §§372.2–372.4 of the Zeckendorf volume. ([raw.githubusercontent.com](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md))

**Definition 20.3 (Mechanical words and future coding).** For a real intercept $\rho$, define the lower and upper mechanical words of slope $\beta$ by
$$
M^{\mathrm{lo}}_\rho(n)
=\lfloor\rho+(n+1)\beta\rfloor-\lfloor\rho+n\beta\rfloor,
$$
$$
M^{\mathrm{up}}_\rho(n)
=\lceil\rho+(n+1)\beta\rceil-\lceil\rho+n\beta\rceil
\qquad(n\ge0).
$$
An integer change in $\rho$ changes neither word. The lower convention assigns digit one to $[1-\beta,1)$; the upper convention assigns it to $(1-\beta,1]$, with the circle point zero represented by one in the latter interval. Define
$$
\Phi(x)=(f(T^n x))_{n\ge0},
\qquad
S((y_n)_{n\ge0})=(y_{n+1})_{n\ge0}.
$$
Here $S$ is the ordinary one-sided shift on binary itineraries.

Attached reference: Berstel, *Sturmian and Episturmian Words* (2007), §3.1, pp. 30–31, gives these lower/upper conventions and their rotation interpretation. ([ligm.univ-eiffel.fr](https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf))

**theorem 20.4 (The exact mechanical coordinate and every split itinerary).** For $x\in K$, take any real lift $\rho$ of
$$
[\rho]=[\beta]-H(x).
$$
If $H(x)\notin E$, then
$$
\Phi(x)=M^{\mathrm{lo}}_\rho=M^{\mathrm{up}}_\rho.
$$
For every $m\ge1$, put $\rho_m=(1-m)\beta$. Then
$$
\Phi(x_m^-)=M^{\mathrm{lo}}_{\rho_m},
\qquad
\Phi(x_m^+)=M^{\mathrm{up}}_{\rho_m}.
$$
For $m=1$ these words differ only at coordinate zero, with respective digits zero and one. For $m\ge2$ they differ exactly at coordinates $m-2,m-1$, where the respective pairs are
$$
10\qquad\text{and}\qquad01.
$$
In particular, a length-$t$ itinerary separates the two members of the fiber above $e_m$ exactly when
$$
t\ge1\quad\text{and}\quad m\le t+1.
$$
The successor respects their orientation until the seam:
$$
Tx_m^\pm=x_{m-1}^\pm\quad(m\ge2),\qquad
Tx_1^-=Tx_1^+=Z(0).
$$
On the natural core the chosen word is exactly
$$
w_n:=f(Z(n))
=\lfloor(n+2)\beta\rfloor-\lfloor(n+1)\beta\rfloor,
$$
so $w=\Phi(Z(0))$ is the lower mechanical word with slope and intercept both equal to $\beta$.

**Proof.** In real phase coordinates the one-digit intervals are $F[C_1]=[a,c]$ and $F[C_0]=[c,b]$. Under the reflected and translated coordinate $[\rho]=[\beta]-[F(x)]$, their interiors become respectively $(1-\beta,1)$ and $(0,1-\beta)$. Moreover,
$$
[\beta]-H(Tx)=[\beta]-H(x)-[\phi]=[\rho+\beta].
$$
Thus rotation by $[\phi]=[\alpha]$ becomes rotation by $[\beta]$ in this coordinate.

If $H(x)\notin E$, its forward phase orbit never meets $e_1$ or $e_2$. Nor can any $\rho+n\beta$ be an integer: that would give
$$
H(x)=[(n+1)\beta]=e_{n+1}.
$$
Reading the two interval interiors therefore gives the lower formula at every time. The upper formula agrees, since neither endpoint of its difference is an integer.

At a split phase, approach $x_m^-$ by natural lifts from the negative phase side, as established in Theorem 20.2. Reflection makes the corresponding intercepts approach $\rho_m$ from above. Every coordinate $f\circ T^n$ is continuous, and floors are right-continuous, so the limit is $M^{\mathrm{lo}}_{\rho_m}(n)$. Approaching $x_m^+$ reverses this direction. The identity
$$
\lim_{\varepsilon\downarrow0}\lfloor z-\varepsilon\rfloor=\lceil z\rceil-1
$$
makes the two subtracted constants cancel, giving the upper formula. This argument applies separately to every coordinate, including the seam coordinate.

Set
$$
D_k=\lceil\rho_m+k\beta\rceil-\lfloor\rho_m+k\beta\rfloor.
$$
Irrationality gives $D_k=0$ precisely at $k=m-1$, and $D_k=1$ at every other nonnegative integer $k$. Since
$$
M^{\mathrm{up}}_{\rho_m}(n)-M^{\mathrm{lo}}_{\rho_m}(n)=D_{n+1}-D_n,
$$
the asserted differences and their exact positions follow. In particular there is no additional endpoint word obtained by choosing the two conventions independently at different times.

For $m\ge2$, rotation sends a same-side sequence approaching $e_m$ to a same-side sequence approaching $e_{m-1}$. Apply continuity of $T$, its successor formula on the natural core, and the side-limit statement of Theorem 20.2. This gives the oriented successor identity. Both alternating sequences are sent to zero by the definition of $T$.

Finally, $H(Z(n))=[n\phi]$ gives the intercept class $[(n+1)\beta]$. Substituting this lift into the time-zero formula yields the displayed formula for $w_n$. At $n=0$ the intercept is $\beta$, not zero. $\square$

Attached reference: Berstel, §3.1, p. 31, calls the equal-slope-and-intercept word the characteristic word; the identification with this particular Zeckendorf observation follows from the proof above. ([ligm.univ-eiffel.fr](https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf))

**theorem 20.5 (Exact temporal complexity and temporal phase cuts).** For every $t\ge0$,
$$
|v_t[K]|=t+1.
$$
The temporal phase cut set is
$$
B_0^{\mathrm{time}}=\varnothing,\qquad
B_t^{\mathrm{time}}=\{e_1,\ldots,e_{t+1}\}\quad(t\ge1).
$$
For positive $t$, the atoms of $\mathcal V_t$ are exactly
$$
A_J=\overline{\{Z(n):H(Z(n))\in J\}}^{\,K},
$$
where $J$ runs through the open arcs complementary to $B_t^{\mathrm{time}}$. Different arcs give different words. Thus the count includes both members of every split fiber without adding singleton boundary atoms.

**Proof.** The empty observation has one value. For $t\ge1$, the possible cuts of the successive readouts are
$$
\bigcup_{i=0}^{t-1}R^{-i}\{e_1,e_2\}
=\bigcup_{i=0}^{t-1}\{e_{i+1},e_{i+2}\}
=\{e_1,\ldots,e_{t+1}\}.
$$
It remains to prove that no two resulting arcs carry the same word; the cut count alone does not establish this.

Use the intercept coordinate from Theorem 20.4 and a representative $0\le\rho<1$. The cuts become zero and the $t$ distinct points
$$
c_j=\{-j\beta\},\qquad1\le j\le t,
$$
where braces denote fractional part. Away from these cuts, the partial sums of the first $t$ lower mechanical digits are
$$
\sum_{i=0}^{j-1}M^{\mathrm{lo}}_\rho(i)
=\lfloor\rho+j\beta\rfloor,\qquad1\le j\le t.
$$
As $\rho$ increases from zero to one, the $j$-th function increases exactly once, at $c_j$, and never decreases. Consequently two different intervals between the sorted cuts have different vectors of partial sums. The digit word determines, and is determined by, those partial sums. Hence these $t+1$ intervals carry $t+1$ different words, including the intervals adjacent to zero on its two sides.

The natural phase orbit is dense and avoids all cuts, so all these words occur on the natural core. Conversely, $v_t$ is continuous with finite discrete target. Every nonempty fiber is open and therefore meets the dense core; there can be no additional word supported only on split points. Each fiber is also closed, and its core intersection is exactly the core phases in the unique arc carrying its word. Density in this clopen fiber proves the formula for $A_J$ and proves that these are all its atoms.

At an endpoint $e_m$, Theorem 20.4 assigns its two lifts the words of the corresponding adjacent arcs whenever $m\le t+1$. For $m>t+1$ the two lifts have the same word and lie in one atom. Continuity and compactness give $H[A_J]=\overline J$: the image is contained in this closed arc and contains the dense natural phases in $J$. Its phase boundaries are therefore exactly the displayed cut set. $\square$

Attached reference: the classical complexity characterization of Sturmian words is stated in Glen–Justin, *Episturmian Words: A Survey*, §1.1, p. 1; Berstel, §2.1, p. 25, Theorem 1 gives the associated eventual-periodicity threshold. The concrete arc distinction and endpoint count here are proved directly. ([arxiv.org](https://arxiv.org/pdf/0801.1655))

**theorem 20.6 (Equal partitions, both exact moduli, and sharpness).** For all $L,t\ge0$,
$$
\mathcal Q_L=\mathcal V_{G_L-1},
\qquad
\ker(q_L)=\ker(v_{G_L-1}),
$$
and more generally
$$
\ker(v_t)\subseteq\ker(q_L)
\quad\Longleftrightarrow\quad t\ge G_L-1,
$$
$$
\ker(q_L)\subseteq\ker(v_t)
\quad\Longleftrightarrow\quad t\le G_L-1.
$$
Thus the least length of consecutive lowest-digit observations determining the first $L$ positional digits is
$$
t_{\min}(L)=G_L-1,
$$
and the least positional depth determining a prescribed length-$t$ itinerary is
$$
L_{\min}(t)=\min\{L\ge0:G_L\ge t+1\}.
$$
In particular $L_{\min}(0)=0$, and for $L\ge1$,
$$
L_{\min}(t)=L
\quad\Longleftrightarrow\quad
G_{L-1}\le t\le G_L-1.
$$

**Proof.** At $L=0$ both relevant partitions have one atom. For $L\ge1$, put $s=G_L-1$. Theorems 20.2 and 20.5 give exactly the same circle cut set for $\mathcal Q_L$ and $\mathcal V_s$. Their atoms are also exactly the same closures of the same natural-core points in the complementary arcs. This proves equality on the full compact carrier, rather than only equality on its natural core. The orientation formulas assign each boundary lift to the same atom in both descriptions.

There is an explicit relabeling. For an admissible prefix $p$, let $N_p=\sum_{j<L}G_jp_j$ and define
$$
A_L(p)=v_s(Z(N_p)).
$$
The point $Z(N_p)$ has prefix $p$. Equality of the two partitions makes $A_L$ a bijection from positional words to temporal words and gives
$$
v_s=A_L\circ q_L.
$$
If $t\le s$, truncate this equality to the first $t$ entries. If $t\ge s$, use
$$
q_L(x)=A_L^{-1}\bigl(\operatorname{pref}_s(v_t(x))\bigr).
$$
These are the required upper-bound factorizations, not cardinality arguments.

For sharpness of the first implication, suppose $t<s$. Take $m=t+2\le G_L$. The pair $x_m^-,x_m^+$ is separated by $q_L$, but its first temporal difference is at index $m-2=t$, which is not included in a length-$t$ observation. Hence no shorter temporal observation determines $q_L$.

For sharpness of the second implication, suppose $t>s$, and take $m=G_L+1$. The pair above $e_m$ has the same $L$-digit prefix, including the case $L=0$, but its first temporal difference is at index $G_L-1=s<t$. Thus $q_L$ cannot determine that longer itinerary. These two pairs establish both converses. Monotonicity and unboundedness of $G_L$ now give the least-index formulas.

The first three depths have no exceptional convention. At depth zero there is one empty word and no circle cut. At depth one,
$$
G_1-1=1,\qquad q_1(x)=v_1(x)=(f(x)),
$$
and the phase cuts are $e_1,e_2$. At depth two the real cylinder intervals are
$$
F[C_{00}]=[c,\alpha^4],\qquad
F[C_{01}]=[\alpha^4,b],\qquad
F[C_{10}]=[a,c],
$$
with $[\alpha^4]=e_3$, and the relabeling is
$$
00\longmapsto01,\qquad
01\longmapsto00,\qquad
10\longmapsto10.
$$
These follow by substituting into the cylinder formula and the first-successor rule. Thus equality is equality of observation partitions, not generally equality of the word-valued maps. The alternating endpoints and all internal double fibers are already included by Theorems 20.2 and 20.4. $\square$

**theorem 20.7 (Generating itinerary and one-sided Sturmian conjugacy).** Let
$$
w_n=\lfloor(n+2)\beta\rfloor-\lfloor(n+1)\beta\rfloor,\qquad
X_\beta=\overline{\{S^n w:n\ge0\}}
\subseteq\{0,1\}^{\mathbb N}.
$$
Then
$$
\Phi:K\longrightarrow X_\beta
$$
is a homeomorphism, and
$$
\Phi\circ T=S\circ\Phi.
$$
The space $X_\beta$ is the one-sided Sturmian subshift of slope $\beta$ with the endpoint conventions of Theorem 20.4. Every orbit in it is dense; its length-$t$ language has exactly $t+1$ words. Every point in it has limiting frequency of digit one equal to the irrational number $\beta$, and is not eventually periodic.

Moreover, $X_\beta$ is a proper closed subset of the positional carrier $K$. The shift in this conjugacy is the restriction of positional deletion to $X_\beta$, not positional deletion on all of $K$.

**Proof.** Each coordinate of $\Phi$ is continuous. If $\Phi(x)=\Phi(y)$, then $v_{G_L-1}(x)=v_{G_L-1}(y)$ for every $L$. Theorem 20.6 gives $q_L(x)=q_L(y)$ for every $L$, hence $x=y$. A continuous injection from compact $K$ into the Hausdorff binary sequence space is a homeomorphism onto its image: images of closed subsets are compact and therefore closed.

Coordinatewise evaluation gives $\Phi(Tx)=S(\Phi(x))$. By continuity, compactness, and density of the natural core,
$$
\Phi[K]
=\overline{\{\Phi(Z(n)):n\ge0\}}
=\overline{\{S^n w:n\ge0\}}
=X_\beta.
$$
Surjectivity of $T$ gives $S[X_\beta]=X_\beta$.

Every finite temporal word occurs on the natural core because its fiber is nonempty and open. Since $T^nZ(0)=Z(n)$, these are exactly the factors of $w$. Theorem 20.5 therefore gives the language count. This is precisely Sturmian factor complexity.

To prove minimality directly, choose any $x\in K$ and any nonempty positional cylinder. Its phase image has a nonempty open arc interior, all of whose fibers lie in that cylinder. The set
$$
\{R^nH(x):n\ge0\}
=H(x)+\{[n\phi]:n\ge0\}
$$
is dense, being a translate of the dense natural phase orbit. Some iterate consequently enters that arc and the corresponding iterate of $x$ enters the cylinder. Cylinders form a basis, so every $T$-orbit is dense. The homeomorphism transfers this property to $X_\beta$.

For either mechanical convention, the number of ones in a prefix of length $n$ differs from $n\beta$ by less than one, by telescoping its defining floor or ceiling differences. Theorem 20.4 supplies one of these formulas for every $x\in K$, including every split point. Hence every itinerary has frequency $\beta$. An eventually periodic binary word has rational limiting frequency, so none is eventually periodic.

The depth-two calculation in Theorem 20.6 shows that no itinerary contains $11$: apply that calculation to $T^j x$ for each $j$. Thus $X_\beta\subseteq K$. The sequence $0^\infty$ belongs to $K$ but has frequency zero, so it does not belong to $X_\beta$. Finally, $S|_K=\sigma$ as coordinate deletion, while the target here is only $X_\beta$. In particular,
$$
\Phi(u)=1w,\qquad\Phi(v)=0w,\qquad
S(1w)=S(0w)=w,
$$
which retains, rather than discards, the two distinct predecessors at the seam. $\square$

Attached reference: Berstel, §3.1, p. 31, identifies irrational mechanical words with Sturmian words and specifies the characteristic intercept. The finite generator and the particular carrier conjugacy are established above. ([ligm.univ-eiffel.fr](https://ligm.univ-eiffel.fr/~berstel/Articles/2007SturmianThessalonique.pdf))

**Definition 20.8 (Topological entropy).** For a continuous self-map $A$ of a compact space and a finite open cover $\mathcal U$, write
$$
\mathcal U_A^{(n)}
=\bigvee_{j=0}^{n-1}A^{-j}\mathcal U,
$$
where the join consists of nonempty intersections. If $N(\mathcal U)$ is the least cardinality of a subcover, define, using natural logarithms,
$$
h_{\mathrm{top}}(A)
=\sup_{\mathcal U}
\limsup_{n\to\infty}\frac1n\log N(\mathcal U_A^{(n)}).
$$
For a finite partition, its number of nonempty atoms will be denoted by $\#\mathcal U$.

**theorem 20.9 (Two different entropies on the same carrier).** The lowest-digit partition is a generating observation for each of the two dynamics, but their iterated observation partitions differ:
$$
h_{\mathrm{top}}(T)=0,\qquad
h_{\mathrm{top}}(\sigma)=\log\phi.
$$
More precisely, for all $L,n\ge1$,
$$
\#\left(\bigvee_{j=0}^{n-1}T^{-j}\mathcal Q_L\right)
=n+G_L-1,
$$
whereas
$$
\#\left(\bigvee_{j=0}^{n-1}\sigma^{-j}\mathcal Q_L\right)
=G_{n+L-1}.
$$
The exact precision/history conversion also has the asymptotics
$$
t_{\min}(L)+1\sim\frac{\phi^{L+2}}{\sqrt5}\quad(L\to\infty),
\qquad
L_{\min}(t)=\log_\phi(t+1)+O(1)\quad(t\to\infty).
$$

**Proof.** Put $\mathcal P=\mathcal Q_1$. Since $f$ is its readout,
$$
\mathcal V_k=\bigvee_{i=0}^{k-1}T^{-i}\mathcal P.
$$
Theorem 20.6 gives $\mathcal Q_L=\mathcal V_s$ with $s=G_L-1\ge1$. Taking $n$ consecutive joins yields
$$
\bigvee_{j=0}^{n-1}T^{-j}\mathcal Q_L
=\mathcal V_{n+s-1}.
$$
Theorem 20.5 counts its atoms as $n+s=n+G_L-1$. Since the $\mathcal Q_L$ form the cylinder basis, this also proves that the future iterates of $\mathcal P$ generate the topology for $T$.

Every finite open cover of $K$ is refined by some $\mathcal Q_L$ with $L\ge1$: choose at each point a cylinder contained in one cover member, take a finite subcover of these cylinders, and increase all their depths to a common $L$. Its $n$-fold temporal join is then refined by the displayed join of $\mathcal Q_L$, so
$$
N(\mathcal U_T^{(n)})\le n+G_L-1.
$$
For every such cover, division of the logarithm by $n$ tends to zero. Nonnegativity of entropy proves $h_{\mathrm{top}}(T)=0$. Thus this conclusion uses a proved generator and all open covers, not merely the complexity of one potentially nongenerating readout.

Positional deletion preserves the no11 constraint and is continuous, since each output coordinate is an input coordinate. Its joined windows reveal exactly the coordinates from zero through $n+L-2$. Therefore
$$
\bigvee_{j=0}^{n-1}\sigma^{-j}\mathcal Q_L
=\mathcal Q_{n+L-1},
$$
which has $G_{n+L-1}$ atoms. In particular, $\mathcal P$ is a generator for $\sigma$ as well. The recurrence and its two initial values give
$$
G_k=\frac{\phi^{k+2}-(-\phi^{-1})^{k+2}}{\sqrt5},
\qquad
\lim_{k\to\infty}\frac{\log G_k}{k}=\log\phi.
$$
The cover $\mathcal P$ gives the entropy lower bound $\log\phi$, since its $n$-fold join consists of $G_n$ pairwise disjoint nonempty sets. For any open cover refined by $\mathcal Q_L$,
$$
N(\mathcal U_\sigma^{(n)})\le G_{n+L-1},
$$
giving the matching upper bound. This proves the second entropy formula directly for the one-sided carrier.

The same closed form gives the stated asymptotic for $G_L=t_{\min}(L)+1$. If $L=L_{\min}(t)\ge1$, then $G_{L-1}\le t<G_L$; the closed form bounds both adjacent terms above and below by fixed positive multiples of $\phi^L$, giving the logarithmic inverse estimate. These statements compare positional depth with the number of consecutive successor observations. $\square$

Attached reference: Schmieding, *Symbolic Dynamics and Subshifts of Finite Type*, §7, Definition 16 on p. 11, Theorem 20 on pp. 13–14, and its golden-mean example on p. 14, give the classical language-growth and spectral-radius entropy formulas. The open-cover argument above establishes the required one-sided formulas without assuming a nongenerating readout suffices. ([s-schmieding.github.io](https://s-schmieding.github.io/SDnotes.pdf))

## 追加锚（本行以下为增补区）
## 21. 增补·Zeckendorf 加法闭图的全部结合单值选择

**定义 21.0（载体、相位与全域选择）。** 取 $\mathbb N=\{0,1,\ldots\}$、$\mathbb N_{>0}=\{1,2,\ldots\}$，并令
$$
\phi=\frac{1+\sqrt5}{2},\qquad \alpha=\phi^{-1},\qquad
G_0=1,\quad G_1=2,\quad G_{j+2}=G_{j+1}+G_j.
$$
令 $Z(n)$ 为自然数 $n$ 的有限 Zeckendorf 规范字按低位到高位补零所得的无限字，且
$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ 对所有 }j\},\qquad 0_K=Z(0).
$$
数字空间取乘积拓扑，置
$$
\mathbb T=\mathbb R/\mathbb Z,\qquad
H(x)=\left[\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j\right],\qquad
P_L(x)=(x_0,\ldots,x_{L-1}),
$$
$$
E_m=[-m\phi]\quad(m\ge1),\qquad E=\{E_m:m\ge1\},\qquad \Sigma=\{-1,+1\}.
$$
定义加法闭图及其输入纤维为
$$
\Gamma=\overline{\{(Z(n),Z(k),Z(n+k)):n,k\in\mathbb N\}}^{K^3},\qquad
\Gamma(x,y)=\{z\in K:(x,y,z)\in\Gamma\}.
$$
全域单值选择是函数 $A:K^2\to K$，满足
$$
\forall x,y\in K,\quad A(x,y)\in\Gamma(x,y).
$$
结合性指 $A(A(x,y),z)=A(x,A(y,z))$ 对全部有序三元组成立；定义不预设交换性、单位或连续性。

**假设 21.1（相位资料与精确保留的闭图纤维前提）。** 采用以下相位资料：$K$ 紧致可度量，$Z[\mathbb N]$ 稠密，$H$ 连续满射，且
$$
H(Z(n))=[n\phi],\qquad H^{-1}(\{0\})=\{0_K\}.
$$
每个 $\theta\notin E$ 的纤维为单点；每个 $\theta\in E$ 的纤维恰为两个不同的点 $z_\theta^{+1},z_\theta^{-1}$。定向标记沿用定义16.3，特别
$$
u=(10)^\omega=z_{E_1}^{+1},\qquad v=(01)^\omega=z_{E_1}^{-1}.
$$
对拓扑结论另采用其具体数字纤维表示：除 $\{u,v\}$ 外，每个二点纤维均为 $\{w0v,w10v\}$，其中 $w$ 为由块 $0$、$10$ 组成的有限块字；两字首次不同的数字位置为 $w$ 的展开长度。[^rro21_phase]

令
$$
\mathcal S(x)=
\begin{cases}
\{s\},&x=z_\theta^s,\ \theta\in E,\ s\in\Sigma,\\
\Sigma,&H(x)\notin E.
\end{cases}
$$
本节明确以下式为数学假设，而非仅假设输出相位正确：对每个 $x,y\in K$，令 $\theta=H(x)+H(y)$，则
$$
\boxed{\quad
\Gamma(x,y)=
\begin{cases}
H^{-1}(\{\theta\}),&\theta\notin E,\\
\{z_\theta^t:t\in\mathcal S(x)\cup\mathcal S(y)\},&\theta\in E.
\end{cases}\quad}
$$
以下结论均以这一精确纤维式为前提。[^rro21_fibers]

**定义 21.2（两个候选与保留、余留部分）。** 对每个 $s\in\Sigma$，令 $j_s:\mathbb T\to K$ 为满足
$$
H(j_s(\theta))=\theta,\qquad j_s(E_m)=z_{E_m}^s
$$
的唯一函数：非分裂相位由其单点纤维决定。置
$$
g_s(m)=j_s(E_m),\qquad b_s(m)=z_{E_m}^{-s},\qquad
I_s=j_s(\mathbb T),\qquad B_s=\{b_s(m):m\ge1\},\qquad c_s=j_s\circ H.
$$
于是 $K=I_s\sqcup B_s$，且 $I_s$ 在每个相位纤维中恰含一点。定义
$$
A_s(x,y)=
\begin{cases}
b_s(m+n),&x=b_s(m),\ y=b_s(n),\ m,n\ge1,\\
j_s(H(x)+H(y)),&\text{其余情形}.
\end{cases}
$$
等价地，输出相位分裂时，只有两个输入均为符号 $-s$ 的分裂点才选择符号 $-s$；其余输入选择符号 $s$。非分裂输出取唯一点。

**定理 21.3（候选存在、完整乘法表及结合性）。** 每个 $A_s$ 均为交换、结合的全域单值选择。其完整乘法表为
$$
A_s(j_s(a),j_s(b))=j_s(a+b)\qquad(a,b\in\mathbb T),
$$
$$
A_s(j_s(a),b_s(m))=A_s(b_s(m),j_s(a))=j_s(a+E_m)\qquad(a\in\mathbb T,\ m\ge1),
$$
$$
A_s(b_s(m),b_s(n))=b_s(m+n)\qquad(m,n\ge1).
$$
每个全域选择，包括这两个候选，均满足
$$
H(A(x,y))=H(x)+H(y),\qquad
A(Z(n),Z(k))=Z(n+k)\quad(n,k\in\mathbb N).
$$
两个候选不同。

**证明。** $\phi$ 无理使各 $E_m$ 两两不同，并给出
$$
0\notin E,\qquad E_m+E_n=E_{m+n},\qquad [n\phi]\notin E\quad(n\ge0).
$$
最后一个断言若失败，则某个正整数倍 $(n+m)\phi$ 为整数。精确纤维式直接给任意选择的相位等式；自然和的相位不分裂，而 $Z(n+k)$ 是该纤维的一点，因此核心加法等式也被强制。

若两个输入均在 $B_s$，它们是同号 $-s$ 的分裂点，纤维式恰强制输出 $b_s(m+n)$。其余情形至少一个输入在 $I_s$：该输入或者不分裂，或者具有符号 $s$，故其符号集合必含 $s$。输出相位分裂时选择 $j_s(\theta)$ 因而合法，非分裂时选择唯一点也合法。这证明选择性及显示的全部乘法表。

乘法表说明 $I_s$ 为双侧理想，且两个 $B_s$ 元素的乘积仍在 $B_s$。对任意有序三元组，若三个输入都在 $B_s$，两种括号方式均得 $b_s(m+n+k)$；否则至少一个输入在 $I_s$，两种括号方式的最终输出均在 $I_s$，且具有相同的总相位。$I_s$ 每相位恰有一点，故两个输出相等。表的左右对称性给交换律。最后
$$
A_{+1}(0_K,u)=u,\qquad A_{-1}(0_K,u)=v,
$$
而 $u\ne v$，所以确有两个不同候选。证毕。

**定理 21.4（不预设交换性的零作用刚性）。** 设 $A$ 为任意结合的全域选择，简记 $x*y=A(x,y)$，并置
$$
c_L(x)=0_K*x,\qquad c_R(x)=x*0_K.
$$
这两个映射均在每个 $H$ 纤维上恒定，而且 $c_L=c_R=:c$。进一步，
$$
H\circ c=H,\qquad c^2=c,
$$
$$
c(x*y)=c(x)*y=x*c(y)=c(x)*c(y).
$$
因此 $M=c(K)$ 为双侧理想，$c$ 是到 $M$ 的半群收缩。存在唯一双射 $j:\mathbb T\to M$，使
$$
H\circ j=\operatorname{id}_{\mathbb T},\qquad j\circ H=c,\qquad
j(a)*j(b)=j(a+b).
$$
特别 $M$ 是以 $0_K=j(0)$ 为单位、以 $j(-a)$ 为 $j(a)$ 之逆元的抽象交换群。

**证明。** 令 $q=[1/2]$。无理性给出
$$
q\notin E,\qquad (q+E)\cap E=\varnothing,\qquad q+q=0.
$$
事实上，$q+E_m=E_n$ 将使 $(m-n)\phi$ 等于一个半整数；若 $m=n$ 则直接矛盾，若 $m\ne n$ 则使 $\phi$ 有理。$q\in E$ 同样不可能。取相位 $q$ 的唯一点 $t$，则相位等式和零纤维唯一性强制
$$
t*t=0_K.
$$

若 $H(x)=H(x')\in E$，则 $t*x,t*x'$ 位于同一个非分裂纤维，故相等；$x*t,x'*t$ 也相等。结合性给
$$
c_L(x)=(t*t)*x=t*(t*x)=t*(t*x')=c_L(x'),
$$
$$
c_R(x)=x*(t*t)=(x*t)*t=(x'*t)*t=c_R(x').
$$
在非分裂纤维上原本只有一点，所以两映射在全部相位纤维上恒定。相位等式又给 $H(c_L(x))=H(c_R(x))=H(x)$。

现在只对有序三元组 $(0_K,x,0_K)$ 使用结合性，得到
$$
c_R(c_L(x))=(0_K*x)*0_K=0_K*(x*0_K)=c_L(c_R(x)).
$$
由于两内层点均与 $x$ 同相位，纤维恒定性使左端为 $c_R(x)$、右端为 $c_L(x)$。故 $c_L=c_R=c$，并由同一纤维恒定性得到 $c^2=c$。

再次分别在左端、右端乘以 $0_K$，得
$$
c(x*y)=(0_K*x)*y=c(x)*y,
$$
$$
c(x*y)=x*(y*0_K)=x*c(y).
$$
于是
$$
c(x)*c(y)=c(x*c(y))=c(c(x*y))=c(x*y).
$$
这些等式证明理想性与收缩同态性质；没有交换两个一般输入。

定义 $j(a)=c(x)$，其中 $H(x)=a$。满射性保证存在这种 $x$，纤维恒定性保证选择无关。$H(j(a))=a$，且 $M$ 中任何同相位两点相等，所以 $j$ 是所述双射。两个像点的乘积属于 $M$，相位为 $a+b$，故等于 $j(a+b)$。圆周加法的单位、逆元和交换律遂逐项给出所述抽象群结构。证毕。

**定理 21.5（全部结合选择的二元分类）。** 对任意全函数 $A:K^2\to K$，以下条件等价：$A$ 是结合的全域单值选择；存在唯一 $s\in\Sigma$ 使 $A=A_s$。因此不存在额外的非交换结合选择。

**证明。** 充分性由定理21.3得到。反向应用定理21.4，取唯一 $s$ 使 $j(E_1)=z_{E_1}^s$。证明
$$
j(E_m)=z_{E_m}^s\qquad(m\ge1).
$$
基步即 $s$ 的定义。若断言对 $m$ 成立，则像群的乘法与同号输入的强制纤维给
$$
j(E_{m+1})=j(E_m)*j(E_1)
=z_{E_m}^s*z_{E_1}^s=z_{E_{m+1}}^s.
$$
所以分支符号不能随 $m$ 改变。非分裂相位本就没有选择，故 $j=j_s$、$M=I_s$、$c=c_s$。

若 $x$ 或 $y$ 在 $I_s$，双侧理想性使 $x*y\in I_s$，相位等式遂强制
$$
x*y=j_s(H(x)+H(y)).
$$
这同时处理非分裂输入、零输入，以及两种有序混合符号输入；例如
$$
z_{E_m}^s*z_{E_n}^{-s}=z_{E_n}^{-s}*z_{E_m}^s=z_{E_{m+n}}^s.
$$
若两输入均不在 $I_s$，它们分别为 $b_s(m),b_s(n)$，同号 $-s$ 的精确纤维强制乘积为 $b_s(m+n)$。所有有序输入对已穷尽，故 $A=A_s$。定理21.3中的不同零切片值给参数唯一性。证毕。

**定理 21.6（严格单位、群部分与余留半群）。** 固定 $s$。$I_s$ 是 $(K,A_s)$ 的唯一最小非空双侧理想，也是唯一最大子群；映射 $j_s$ 给出抽象群同构
$$
(\mathbb T,+)\cong(I_s,A_s),\qquad
j_s(a)^{-1}=j_s(-a).
$$
映射 $m\mapsto b_s(m)$ 给出半群同构
$$
(\mathbb N_{>0},+)\cong(B_s,A_s),
$$
其与群部分的全部混合乘积已由定理21.3确定。唯一幂等元为 $0_K$，但整个 $K$ 没有严格左单位，也没有严格右单位。以幂等元 $0_K$ 构成的局部幺半群恰为
$$
0_K*K*0_K=I_s,
$$
其全部元素均为该局部幺半群的可逆元；不能将其称为整个 $K$ 的单位群。

关系 $\Gamma$ 的唯一弱左、弱右单位均为 $0_K$，但它不是关系的严格单位。结合性对于上述函数单位障碍不可删除：存在以 $0_K$ 为严格双侧单位的非结合全域选择。

**证明。** 群同构、双侧理想和正整数半群同构分别来自定理21.4与乘法表；后一个映射的单射性由各 $E_m$ 不同得到。若 $x*x=x$，则 $2H(x)=H(x)$，所以 $H(x)=0$，进而 $x=0_K$；而 $0_K*0_K=0_K$。

任一子群的单位必幂等，因而只能是 $0_K$。该子群中的 $x$ 必满足 $c_s(x)=0_K*x=x$，即 $x\in I_s$，故 $I_s$ 是唯一最大子群。若 $J$ 为非空双侧理想，取 $x\in J$，则 $c_s(x)=0_K*x\in J\cap I_s$。再与其像群逆元相乘得 $0_K\in J$，继而任意 $a\in\mathbb T$ 均满足 $j_s(a)=0_K*j_s(a)\in J$。因此 $I_s\subseteq J$，证明最小理想断言。

若 $e$ 是整个 $K$ 的严格左单位，则 $e*0_K=0_K$，相位等式迫使 $e=0_K$。然而
$$
0_K*b_s(m)=g_s(m)\ne b_s(m).
$$
故左单位不存在；严格右单位同理由 $0_K*e=0_K$ 和 $b_s(m)*0_K=g_s(m)$ 排除。收缩等式给 $0_K*K*0_K=I_s$。特别地，虽然
$$
b_s(m)*Z(m)=Z(m)*b_s(m)=0_K,
$$
但 $b_s(m)$ 不在任何子群中：乘积为 $0_K$ 的方程不能替代单位作用条件。

由 $\mathcal S(0_K)=\Sigma$ 及精确纤维式，
$$
\Gamma(0_K,x)=\Gamma(x,0_K)=H^{-1}(\{H(x)\})\ni x.
$$
任一弱左或弱右单位对输入 $0_K$ 的相位条件都迫使它等于 $0_K$，而分裂纤维不是单点，故关系严格单位不存在。

最后定义
$$
\widehat A_s(x,y)=
\begin{cases}
y,&x=0_K,\\
x,&x\ne0_K,\ y=0_K,\\
A_s(x,y),&x\ne0_K,\ y\ne0_K.
\end{cases}
$$
刚证的弱单位包含式保证这是全域选择，并以 $0_K$ 为严格双侧单位。取定理21.4中的半转点 $t$。相位 $q+E_1$ 非分裂且非零，因此
$$
\widehat A_s(\widehat A_s(t,t),b_s(1))=b_s(1),
$$
$$
\widehat A_s(t,\widehat A_s(t,b_s(1)))=g_s(1).
$$
第二式的两次外于零输入的运算分别经过非分裂相位 $q+E_1$ 和分裂相位 $E_1$，最后选择符号 $s$。两个结果不同，故这个严格有单位的选择不结合。证毕。

**定理 21.7（具体半群模型、相位商与理想商）。** 在不交并
$$
\mathscr M=(\mathbb T\times\{0\})\sqcup(\mathbb N_{>0}\times\{1\})
$$
上定义
$$
(a,0)\circ(b,0)=(a+b,0),\qquad
(m,1)\circ(n,1)=(m+n,1),
$$
$$
(a,0)\circ(m,1)=(m,1)\circ(a,0)=(a+E_m,0).
$$
双射
$$
F_s(a,0)=j_s(a),\qquad F_s(m,1)=b_s(m)
$$
是到 $(K,A_s)$ 的半群同构。此模型正是二元链 $0<1$ 上的强半格半群：下层为圆周群，上层为正整数加法半群，唯一非恒等连接同态为 $m\mapsto E_m$。[^rro21_semilattice] 自然核心及相位在此模型中分别为
$$
Z(n)=F_s([n\phi],0),\qquad
(H\circ F_s)(a,0)=a,\qquad(H\circ F_s)(m,1)=E_m.
$$

相位相等关系是半群同余，且
$$
\ker c_s=\ker H,\qquad (K,A_s)/{\ker H}\cong(\mathbb T,+).
$$
这里核均指相等关系核。更精确地，对所有 $z\in\Gamma(x,y)$，
$$
c_s(z)=A_s(c_s(x),c_s(y))=j_s(H(x)+H(y)).
$$
但是 $A_s$ 本身不能经 $H\times H$ 因子化，且函数 $(x,y)\mapsto j_s(H(x)+H(y))$ 并非 $\Gamma$ 的全域选择。

另将整个理想 $I_s$ 压为一个吸收点 $\bot$，得到的 Rees 商为
$$
Q=\mathbb N_{>0}\sqcup\{\bot\},\qquad
m\cdot n=m+n,\qquad \bot\cdot q=q\cdot\bot=\bot.
$$
因此 $(K,A_s)$ 是圆周群的收缩理想扩张。[^rro21_retract] 吸收点 $\bot$ 不是自然数加法的单位；该理想商也不是相位商。

**证明。** 显示的模型乘法与定理21.3逐项一致，故 $F_s$ 保乘法且双射。连接映射保乘法正是 $E_{m+n}=E_m+E_n$；二元链中的其余连接映射为恒等，复合相容性随即成立。这给出所述强半格构造，而不要求上层为群。自然核心与相位的显示式由定义直接得到。

$c_s=j_sH$ 且 $j_s$ 单射，故两相等关系核一致；相位等式使这个核为同余，$H$ 的满射性给所述商同构。对任意允许输出 $z$，其相位已固定，应用 $c_s$ 得到同一个 $j_s(H(x)+H(y))$；乘法表又给另一等号。然而
$$
A_s(b_s(m),b_s(n))=b_s(m+n),\qquad
A_s(g_s(m),g_s(n))=g_s(m+n),
$$
两对输入逐槽同相位而输出不同，所以 $A_s$ 不能经 $H\times H$ 因子化。同时
$$
j_s(E_m+E_n)=g_s(m+n)\notin
\Gamma(b_s(m),b_s(n))=\{b_s(m+n)\},
$$
排除了直接由相位截面回填整个乘法的办法。

令理想商映射在 $I_s$ 上取 $\bot$，在 $b_s(m)$ 上取 $m$。混合乘积落入 $I_s$，两个余留点的乘积为 $b_s(m+n)$，所以商乘法恰为显示的 $Q$。收缩同态是 $c_s$。这个商把全部自然核心送到 $\bot$，相位商则保留 $[n\phi]$，故不能混同。证毕。

**定理 21.8（闭图障碍与零切片的精确连续点）。** 不存在联合连续的全域单值选择，无须在此断言中假设结合性。[^rro21_graph] 对两个结合选择，
$$
A_s(0_K,x)=A_s(x,0_K)=c_s(x),
$$
且这两个零切片作为 $K\to K$ 的函数，其连续点集恰为 $I_s$，不连续点集恰为 $B_s$。因此 $A_s$ 也不是分别连续的二元运算。

**证明。** 若选择 $A$ 联合连续，其函数图在 $K^3$ 中闭：它是映射 $(x,y,z)\mapsto(A(x,y),z)$ 下闭对角线的原像。由核心加法等式，此闭图包含全部自然加法三元组，因此包含它们的闭包 $\Gamma$。但
$$
(0_K,u,u),(0_K,u,v)\in\Gamma,\qquad u\ne v,
$$
与函数图在一个输入处只有一个输出矛盾。

固定 $s$。函数 $c_s$ 在 $I_s$ 上为恒等，在 $b_s(m)$ 处改取 $g_s(m)$。对每个 $L\ge1$，令
$$
D_L=\{b_s(m):P_L(b_s(m))\ne P_L(g_s(m))\}.
$$
这是有限集：接缝纤维至多贡献一个点；其余纤维为 $\{w0v,w10v\}$，只有展开长度小于 $L$ 的 $w$ 才可能贡献，而这样的有限块字只有有限多个。这个论证不依赖分支方向的奇偶性。

给定 $x\in I_s$，集合
$$
U_L=P_L^{-1}(\{P_L(x)\})\setminus D_L
$$
是包含 $x$ 的开邻域。每个 $y\in U_L$ 满足
$$
P_L(c_s(y))=P_L(y)=P_L(x)=P_L(c_s(x)).
$$
有限前缀柱集构成拓扑基，故 $c_s$ 在 $x$ 连续。

反之，固定 $b_s(m)$ 并截断其数字，令
$$
n_L=\sum_{j<L}G_j\,b_s(m)_j,\qquad x_L=Z(n_L).
$$
截断后补零仍是合法规范字，故 $x_L\to b_s(m)$。自然核心不分裂，所以
$$
c_s(x_L)=x_L\longrightarrow b_s(m)\ne g_s(m)=c_s(b_s(m)).
$$
因此每个余留点都是不连续点。零切片等式来自乘法表，全部断言得证。

**定理 21.9（像群的抽象结构与子空间拓扑）。** 给 $I_s$ 赋予 $K$ 的子空间拓扑。限制
$$
H|_{I_s}:I_s\longrightarrow\mathbb T
$$
是连续的抽象群同构，但不是同胚；其逆映射 $j_s$ 的连续点恰为 $\mathbb T\setminus E$。空间 $I_s$ 稠密、真包含于 $K$、非紧且零维，因此不与通常圆周同胚。更强地，限制运算 $A_s|_{I_s^2}$ 也不分别连续，故这个子空间群不是拓扑群。

**证明。** 先使用紧致单点纤维事实：若 $\theta_k\to\theta$，且 $H^{-1}(\{\theta\})=\{x\}$，则任意满足 $H(x_k)=\theta_k$ 的点列均趋于 $x$。否则可在某个 $x$ 的开邻域外取子列，再由紧致可度量性取收敛子列；连续性使其极限仍在该单点纤维，与处于邻域外矛盾。

这立即证明 $j_s$ 在非分裂相位连续。固定 $E_m$，使用证明21.8中的 $Z(n_L)\to b_s(m)$，则
$$
[n_L\phi]\longrightarrow E_m,\qquad
j_s([n_L\phi])=Z(n_L)\longrightarrow b_s(m)\ne j_s(E_m).
$$
所以 $j_s$ 在每个分裂相位不连续。$H|_{I_s}$ 的连续性、双射性及保群运算性质已分别来自 $H$ 与乘法表。

自然核心包含于 $I_s$，故 $I_s$ 稠密；$B_s$ 非空，故 $I_s$ 是真子集。若 $I_s$ 紧，则它在 Hausdorff 空间 $K$ 中闭，与稠密且真包含矛盾。有限前缀柱集的交给出 $I_s$ 的开闭基；不同点可被这样的集合分离，故 $I_s$ 全不连通，而通常圆周连通，所以不存在空间同胚。

最后仍固定 $m\ge1$，令
$$
p_L=Z(n_L)\longrightarrow b_s(m),\qquad y_L=Z(n_L+m)\in I_s.
$$
因为
$$
H(y_L)=[(n_L+m)\phi]=H(p_L)-E_m\longrightarrow0,
$$
零相位的单点纤维事实给 $y_L\to0_K$。但是
$$
A_s(g_s(m),y_L)=j_s(E_m+[(n_L+m)\phi])=p_L,
$$
$$
A_s(g_s(m),0_K)=g_s(m)\ne b_s(m).
$$
第一列在 $K$ 中趋于 $b_s(m)$，因 Hausdorff 性不可能趋于 $g_s(m)$，故在 $I_s$ 中也不趋于所需值。固定 $g_s(m)$ 的乘法切片在 $0_K$ 处不连续。这直接否定子空间上的分别连续性，而不是仅由非紧性推断。证毕。

[^rro21_phase]: 《CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF》，定义371.1、定理371.2及372.2—372.4；固定提交 c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb。所用资料为紧数字载体、自然相位、全部相位纤维及有限块字形式。 ([raw.githubusercontent.com](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md))

[^rro21_fibers]: 《RECURSIVE_RELATIONAL_OBSERVATION》，定义16.0、16.3及定理16.4的纤维公式；固定提交 c74985438ae17d205509255934bbd3ecf1f94d71。本节将该公式完整列为假设21.1。 ([raw.githubusercontent.com](https://raw.githubusercontent.com/the-omega-institute/trureturing/c74985438ae17d205509255934bbd3ecf1f94d71/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md))

[^rro21_semilattice]: Jiangang Zhang, Yuhui Yang, Ran Shen, *The strong semilattice of $\pi$-groups*, European Journal of Pure and Applied Mathematics 11(3) (2018), 589–597，DOI: 10.29020/nybg.ejpam.v11i3.3274。所用为第1节、第589页的强半格半群一般构造及连接同态条件，不使用后文关于各分量为 $\pi$-群的分类。 ([ejpam.com](https://www.ejpam.com/ejpam/article/view/3274/661))

[^rro21_retract]: Attila Nagy, *On left legal semigroups*, arXiv:2301.08793v2 (2023)，第2节关于 Rees 商、理想扩张与收缩理想的定义；不使用该文针对左合法半群的结构定理。 ([arxiv.org](https://arxiv.org/html/2301.08793v2))

[^rro21_graph]: 《CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF》，定理377.1，同一固定提交；联合连续自然加法延拓的障碍。定理21.8另由加法图的闭包与二点输出给出直接证明。 ([raw.githubusercontent.com](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md))

## 追加锚（本行以下为增补区）
## 22. Exact continuity loci and measurable outputs of closed Zeckendorf addition

**Definition 22.1 (Digit space and the joint closed graph).** Work in ZFC, with zero included in $\mathbb N$. Put
$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,\qquad
\phi=\frac{1+\sqrt5}{2},\quad \alpha=\phi^{-1},\quad r=-\alpha.
$$
Let $K$ consist of the infinite binary sequences $x$ satisfying $x_jx_{j+1}=0$, written from low to high digits. Let $Z(n)$ denote the legal Zeckendorf expansion of $n$, padded with zeros, and set
$$
d_K(x,y)=\sum_{j\geq0}2^{-j-1}|x_j-y_j|,\qquad
X=K^2,\qquad
d_X((x,y),(x',y'))=\max\{d_K(x,x'),d_K(y,y')\}.
$$
For a finite legal digit word $p$ of length $L$, let $C_p$ be its cylinder in $K$ and put
$$
S_p=\sum_{j<L}(-1)^{j+1}\alpha^{j+2}p_j.
$$
The empty word defines $C_{\varnothing}=K$. Define
$$
F(x)=\sum_{j\geq0}(-1)^{j+1}\alpha^{j+2}x_j,\qquad
H(x)=[F(x)]\in\mathbb T=\mathbb R/\mathbb Z,
$$
$$
I=[-\alpha,\alpha^2],\quad
\gamma(n)=[n\phi],\quad
E=\{[-m\phi]:m\geq1\},\quad
0_K=Z(0),\quad u=(10)^\infty,\quad v=(01)^\infty.
$$
Concatenations such as $0v$ and $10v$ retain this digit order. The relation and its input fibers are
$$
\Gamma=\overline{\{(Z(n),Z(m),Z(n+m)):n,m\in\mathbb N\}}^{\,K^3},
\qquad
\Gamma(x,y)=\{z\in K:(x,y,z)\in\Gamma\}.
$$
Write $X_{\mathrm{fin}}=Z[\mathbb N]^2$ and $\Theta(x,y)=H(x)+H(y)$. All references to $\Gamma$ concern this joint graph, not merely the equation $H(z)=\Theta(x,y)$.

**Assumption 22.2 (Precisely imported phase and joint-fiber classification).** Assume the phase classification of [the fixed phase source, §§371–372, particularly Theorems 372.2–372.4](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md): $F[K]=I$; each $H$-fiber outside $E$ is a singleton; and each fiber over $\theta\in E$ consists of two distinct labeled points $z_\theta^{+1},z_\theta^{-1}$. Use exactly the labels of [the fixed addition source, Definition 16.3 and Theorem 16.4](https://raw.githubusercontent.com/the-omega-institute/trureturing/c74985438ae17d205509255934bbd3ecf1f94d71/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md), so in particular
$$
z_{[-\phi]}^{+1}=u,\quad z_{[-\phi]}^{-1}=v,\qquad
z_{[-2\phi]}^{+1}=0v,\quad z_{[-2\phi]}^{-1}=10v.
$$
Define
$$
\mathcal S(x)=
\begin{cases}
\{s\},&H(x)\in E\text{ and }x=z_{H(x)}^s,\quad s\in\{-1,+1\},\\
\{-1,+1\},&H(x)\notin E.
\end{cases}
$$
Assume the following statement about the actual joint closure in Definition 22.1, with $\theta=\Theta(x,y)$:
$$
\Gamma(x,y)=
\begin{cases}
H^{-1}(\{\theta\}),&\theta\notin E,\\
\{z_\theta^{+1}\},&\theta\in E,\ \mathcal S(x)=\mathcal S(y)=\{+1\},\\
\{z_\theta^{-1}\},&\theta\in E,\ \mathcal S(x)=\mathcal S(y)=\{-1\},\\
\{z_\theta^{+1},z_\theta^{-1}\},&\theta\in E\text{ and neither same-sign case holds}.
\end{cases}
$$
Every theorem below is conditional on this explicitly imported assumption; no selection law is included in it.

**theorem 22.3 (Compactness, finite-core density, and interiors of cylinder phases).** The space $K$ is compact, its cylinders form a countable clopen base, and $Z[\mathbb N]$ is dense. The maps $F,H$ are continuous, $H$ is onto, and
$$
H(Z(n))=\gamma(n),\qquad \gamma(n)\notin E,\qquad
\Gamma(Z(n),Z(m))=\{Z(n+m)\}.
$$
Both $\gamma[\mathbb N]$ and $E$ are dense in $\mathbb T$. Every nonempty cylinder has a phase image containing a nonempty open arc. More precisely,
$$
F[C_p]=
\begin{cases}
I,&L=0,\\
S_p+r^L I,&L>0\text{ and }p_{L-1}=0,\\
S_p+r^{L+1}I,&L>0\text{ and }p_{L-1}=1.
\end{cases}
$$

**Proof 22.3.** The series defining $d_K$ is a metric by the coordinatewise triangle inequality and positivity of every coordinate weight. Agreement in the first $L$ coordinates gives distance at most $2^{-L}$; distance less than $2^{-L}$ forces such agreement. Thus the metric gives the product topology, with the stated countable clopen cylinder base. From any sequence in $K$, successively choose infinite subsequences constant in the next coordinate and take a diagonal subsequence. Its coordinatewise limit is still legal, since each adjacent pair eventually stabilizes. The tail estimate for $d_K$ gives metric convergence. Sequential compactness of a metric space implies compactness, proving the assertion for $K$ and hence for its finite products.

For $x\in K$ put $N_L=\sum_{j<L}G_jx_j$. Truncating at $L$ and appending zeros is legal, so uniqueness of the finite Zeckendorf expansion identifies it with $Z(N_L)$. Its distance from $x$ is at most $2^{-L}$. This proves core density, also in $X$. Since $1-\alpha=\alpha^2$, the defining series for $F$ has uniform tail bound
$$
\sum_{j\geq L}\alpha^{j+2}=\alpha^L.
$$
Consequently $F$ and then $H$ are continuous. The interval $I$ has length one, so Assumption 22.2 implies that $H$ is onto.

The identity
$$
\phi G_j-G_{j+1}=(-1)^{j+1}\alpha^{j+2}
$$
holds at the first two indices. Both sides satisfy the Fibonacci recurrence, since $r^2=r+1$, so it holds at every index. Multiplication by the finitely many digits of $Z(n)$ and summation give
$$
F(Z(n))=\phi n-\sum_{j\geq0}G_{j+1}Z(n)_j,
$$
whose second term is an integer. This proves the phase identity. If $\gamma(n)=[-m\phi]$ with $m\geq1$, then $(n+m)\phi$ is an integer, contradicting irrationality of $\phi$. The sum phase is therefore outside $E$, and its unique inverse under $H$ is $Z(n+m)$; Assumption 22.2 gives the asserted natural-input fiber.

For every nonempty open subset of $\mathbb T$, its inverse image under the continuous surjection $H$ is nonempty and open, hence meets the finite core. Thus $\gamma[\mathbb N]$ is dense. The identity
$$
E=[-\phi]-\gamma[\mathbb N]
$$
proves density of $E$.

For the cylinder formula, a prefix ending in zero permits every legal tail immediately after it, and splitting the series gives $F(pt)=S_p+r^L F(t)$. A prefix ending in one forces a zero next, after which every legal tail is permitted; splitting now gives $F(p0t)=S_p+r^{L+1}F(t)$. Surjectivity of $F$ onto $I$ proves both equalities, including both directions of each range assertion. The corresponding interval lengths are $\alpha^L$ and $\alpha^{L+1}$, respectively, and are positive. Projection to the circle therefore contains a nonempty open arc. An odd power of $r$ reverses interval orientation but does not remove these interiors. The empty-prefix case is $F[K]=I$. This proves all assertions.

**theorem 22.4 (Upper semicontinuity and actual joint approximation).** The relation $\Gamma$ is compact with nonempty compact fibers. For every closed $C\subseteq K$, the hit set
$$
\operatorname{Hit}(C)=\{\xi\in X:\Gamma(\xi)\cap C\ne\varnothing\}
$$
is closed. Consequently, for every $\xi\in X$ and open $V\supseteq\Gamma(\xi)$, some neighborhood $U$ of $\xi$ satisfies $\Gamma(\eta)\subseteq V$ for all $\eta\in U$. For open $O\subseteq K$, the hit set $\operatorname{Hit}(O)$ is $F_\sigma$. Every $(x,y,z)\in\Gamma$ admits natural-number sequences $n_j,m_j$ such that
$$
(Z(n_j),Z(m_j),Z(n_j+m_j))\longrightarrow(x,y,z).
$$

**Proof 22.4.** Closedness in compact $K^3$ gives compactness. Fibers are closed subsets of $K$. Their nonemptiness follows also directly from the closure construction: approximate each input by finite truncations, take a convergent subsequence of their actual sums in compact $K$, and use closedness. For closed $C$, the set $\Gamma\cap(X\times C)$ is compact; its projection to $X$ is compact and hence closed. This projection is exactly $\operatorname{Hit}(C)$. If $\Gamma(\xi)\subseteq V$, the point $\xi$ is outside the closed set $\operatorname{Hit}(K\setminus V)$, and its open complement is the required neighborhood. An open $O$ is the union of the countably many cylinders contained in it. Its hit set is the corresponding countable union of closed hit sets.

These are upper semicontinuity and Effros measurability in the sense of [B. Cascales, *Measurability and semi-continuity of multifunctions*, Definitions 1.3–1.4, p. 4](https://webs.um.es/beca/Investigacion/semicontinuityofmultifunctions.pdf). They also verify the open-hit measurability condition of the Kuratowski–Ryll-Nardzewski theorem as stated in [B. Cascales, V. Kadets and J. Rodríguez, *Measurability and Selections of Multi-Functions in Banach Spaces*, Theorem A, p. 1](https://webs.um.es/beca/Investigacion/PropertyP_11.pdf); the target here is separable metric and the values are nonempty and complete.

Finally, equip $K^3$ with its maximum product metric. For each integer $j\geq1$, the ball of radius $1/j$ about $(x,y,z)$ meets the set whose closure defines $\Gamma$. Choose one of its actual addition triples. The same choice supplies both input approximations and their actual sum, all within $1/j$. This proves the joint convergence; no independently chosen output or merely marginal realization is used.

**Definition 22.5 (Selections and the two loci).** A point selection is any function $A:X\to K$ with $A(\xi)\in\Gamma(\xi)$ for every $\xi$, without a measurability or algebraic requirement. Define
$$
D=\{\xi\in X:|\Gamma(\xi)|=2\},\qquad G=X\setminus D,
\qquad
D_n=\{\xi\in X:\operatorname{diam}_{d_K}\Gamma(\xi)\geq1/n\}\quad(n\geq1).
$$
Also put $K_s=\{z_\theta^s:\theta\in E\}$ for $s\in\{-1,+1\}$. A set is nowhere dense when its closure has empty interior, meagre when it is a countable union of nowhere dense sets, $F_\sigma$ when it is a countable union of closed sets, and $G_\delta$ when it is a countable intersection of open sets.

**theorem 22.6 (The same exact continuity locus for every point selection).** Every point selection satisfies
$$
\overline{\operatorname{graph}(A)}=\Gamma,
\qquad
\operatorname{Cont}(A)=G.
$$
Every $D_n$ is closed and nowhere dense, and
$$
D=\bigcup_{n\geq1}D_n,\qquad
G=\bigcap_{n\geq1}(X\setminus D_n).
$$
Thus $D$ is meagre $F_\sigma$ and $G$ is dense $G_\delta$. Its exact phase-and-sign description is
$$
D=\Theta^{-1}(E)\setminus
\bigl((K_{+1}\times K_{+1})\cup(K_{-1}\times K_{-1})\bigr).
$$

**Proof 22.6.** Every selection graph is contained in the closed set $\Gamma$. By Theorem 22.3 it contains every actual finite addition triple, whose closure is $\Gamma$. This proves the graph equality. More precisely, for every $z\in\Gamma(\xi)$, Theorem 22.4 gives input pairs $\xi_j\in X_{\mathrm{fin}}$ tending to $\xi$ whose actual sums tend to $z$. At these inputs the selection is forced to be that actual sum. Conversely, any limit of selection outputs along inputs tending to $\xi$ belongs to $\Gamma(\xi)$ by closedness. Thus the output limits along approaching inputs are exactly the full fiber.

If $\Gamma(\xi)=\{z\}$, upper semicontinuity applied to the ball of radius $\varepsilon$ about $z$ gives a neighborhood on which all permissible outputs, and hence the values of $A$, lie in that ball. Since $A(\xi)=z$, this is continuity at $\xi$. If the fiber contains distinct $z_0,z_1$, use the preceding joint approximation separately for these two outputs. This gives two sequences of actual natural input pairs converging to the same $\xi$, along which $A$ tends respectively to $z_0$ and $z_1$. Continuity at $\xi$ would make both limits equal to $A(\xi)$, which is impossible. This proves the exact locus without any regularity assumption on $A$.

Suppose $\xi_j\in D_n$ and $\xi_j\to\xi$. Compactness of the fibers makes their diameters attained, so choose $z_j,w_j\in\Gamma(\xi_j)$ with $d_K(z_j,w_j)\geq1/n$. A subsequence of $(z_j,w_j)$ converges in compact $K^2$, say to $(z,w)$. Closedness gives $z,w\in\Gamma(\xi)$, and continuity of the metric gives $d_K(z,w)\geq1/n$. Hence $D_n$ is closed. It is disjoint from the dense set $X_{\mathrm{fin}}$, so it has empty interior and is nowhere dense. A fiber has two points exactly when its diameter is positive, which is equivalent to membership in some $D_n$. This proves the displayed countable union and intersection. The set $G$ contains $X_{\mathrm{fin}}$, so it is dense.

The final formula is exactly the case distinction of Assumption 22.2: an exceptional sum phase gives two outputs unless both inputs carry the same forced sign. In particular, exceptional sum phase alone is not a sufficient criterion for discontinuity.

**theorem 22.7 (Density with a constant two-output Cantor family).** Every nonempty open $W\subseteq X$ contains a compact set $M$ homeomorphic to $\{0,1\}^{\mathbb N}$ and some $\theta\in E$ such that
$$
\Gamma(\xi)=\{z_\theta^{+1},z_\theta^{-1}\}\quad(\xi\in M),
$$
while both input phases of every $\xi\in M$ lie outside $E$. In particular, $D$ is dense; $G$ has empty interior; and no point selection is continuous on any nonempty open subspace of $X$.

**Proof 22.7.** Choose a nonempty cylinder rectangle $C_p\times C_q\subseteq W$. By Theorem 22.3 choose nonempty open arcs $J\subseteq H[C_p]$ and $L\subseteq H[C_q]$. The sum $J+L$ is nonempty and open, since it is a union of translates of $L$. Density of $E$ supplies
$$
\theta\in E\cap(J+L).
$$
Then $B=J\cap(\theta-L)$ is nonempty and open. Exclude the countable set
$$
T=E\cup(\theta-E).
$$
There is a Cantor set $C\subseteq B\setminus T$, as the following construction shows. Inside a proper circle-coordinate arc contained in $B$, choose a nondegenerate closed interval. Enumerate the points of $T$ in that arc. At stage $n$, replace each interval already chosen by two disjoint nondegenerate closed subintervals in its interior, avoiding the first $n$ enumerated points, with lengths at most $2^{-n}$. Removing finitely many points from a nonempty interval leaves room for both children. Intersect the resulting nested finite unions. Each binary branch determines a unique point because interval lengths tend to zero; distinct branches give distinct points because siblings are disjoint. Every point in the intersection determines its branch. The branch map is continuous by the length bound and is a homeomorphism from compact binary sequence space onto the intersection. Every enumerated point is excluded at its stage, proving the assertion about $C$.

For $\beta\notin E$, let $h(\beta)$ be the unique element of $H^{-1}(\{\beta\})$. This inverse is continuous on the subspace $\mathbb T\setminus E$. Indeed, if $V$ is open in $K$ and contains $h(\beta)$, then the compact set $H(K\setminus V)$ does not contain $\beta$. Its complement is a neighborhood of $\beta$ whose nonexceptional phases have their unique inverses in $V$.

Define
$$
j:C\longrightarrow X,\qquad j(\beta)=(h(\beta),h(\theta-\beta)).
$$
Both inverses are defined because $C$ avoids $E$ and $\theta-E$. The map is continuous and injective: its first coordinate phase recovers $\beta$. Its image $M$ is compact, and the compact-to-Hausdorff continuous bijection makes $j$ a homeomorphism onto $M$. Since $\beta\in J$ and $\theta-\beta\in L$, uniqueness of each inverse and the inclusions of these arcs in the cylinder images place $M$ inside $C_p\times C_q$.

At every such input both sign sets are $\{-1,+1\}$, while the sum phase is $\theta\in E$. Assumption 22.2 therefore gives both outputs, with neither same-sign exclusion applicable. Hence $M\subseteq D\cap W$, proving density by actual cylinder interiors, not by countability of $E$ or marginal density. Density of $D$ gives empty interior of $G$. If a selection were continuous on a nonempty open subspace, choose a point of $D$ there. The actual input sequences proving its discontinuity are eventually in that open subspace, a contradiction.

**Definition 22.8 (Regularity and ordered selections).** A map into a topological space $Y$ is of Baire class one here precisely when it is a pointwise limit of continuous maps with values in that same $Y$. A Borel map has Borel inverse images of open sets. A map is Baire-property measurable when every such inverse image differs from an open set by a meagre set. These latter two uses of Baire are not identified. A map is universally measurable when its open-set inverse images are measurable for the completion of every Borel probability measure on its domain. Define
$$
e:K\longrightarrow[0,1],\qquad e(x)=\sum_{j\geq0}\frac{2x_j}{3^{j+1}}.
$$
The lexicographic order on $K$ compares the first differing digit, with zero smaller than one. Write $A_{\min}(\xi)$ and $A_{\max}(\xi)$ for the least and greatest members of $\Gamma(\xi)$ in this order. Their existence and their target-valued approximation are proved next. The distinction between Borel class one and same-target Baire class one is also explicit in [V. V. Srivatsa, *Baire class 1 selectors for upper semicontinuous set-valued maps*, Transactions of the American Mathematical Society 337 (1993), 609–624, Remark 2.2 and Corollaries 2.2–2.3, p. 620](https://scispace.com/pdf/baire-class-1-selectors-for-upper-semicontinuous-set-valued-290347w76e.pdf).

**theorem 22.9 (Borel selections with continuous approximants taking values in the actual digit space).** The maps $A_{\min},A_{\max}:X\to K$ exist, are Borel, and are of Baire class one with target $K$. The real-valued map $e\circ A_{\min}$ is lower semicontinuous and $e\circ A_{\max}$ is upper semicontinuous. Their Baire-one assertion does not require passing through continuous approximants outside $K$.

**Proof 22.9.** The series for $e$ converges uniformly and so defines a continuous map. If $x,y$ first differ at index $j$, with $x_j=0$ and $y_j=1$, then
$$
e(y)-e(x)\geq \frac{2}{3^{j+1}}-\sum_{k>j}\frac{2}{3^{k+1}}
=\frac1{3^{j+1}}>0.
$$
Thus $e$ is injective and preserves the stated order. Compactness makes it a homeomorphism onto $e[K]$. The image of each nonempty compact fiber has an attained minimum and maximum, giving unique $A_{\min}$ and $A_{\max}$. Moreover,
$$
\{\xi:e(A_{\min}(\xi))\leq t\}=\operatorname{Hit}(\{z:e(z)\leq t\}),
$$
$$
\{\xi:e(A_{\max}(\xi))\geq t\}=\operatorname{Hit}(\{z:e(z)\geq t\}).
$$
These sets are closed by Theorem 22.4, proving the two scalar semicontinuity claims.

For a same-target construction, partition $X$ by the first $n$ digits of each input. This is a finite clopen partition. Denote the cell containing $\xi$ by $C_n(\xi)$, and define
$$
T_n(\xi)=\bigcup_{\eta\in C_n(\xi)}\Gamma(\eta).
$$
It is a nonempty compact set, being the projection of $\Gamma\cap(C_n(\xi)\times K)$. These sets decrease with $n$, and
$$
\bigcap_{n\geq1}T_n(\xi)=\Gamma(\xi).
$$
The inclusion from right to left is immediate. For the reverse inclusion, if $z$ belongs to every $T_n(\xi)$, choose $\eta_n\in C_n(\xi)$ with $z\in\Gamma(\eta_n)$. The cell diameter is at most $2^{-n}$, so $\eta_n\to\xi$. Closedness gives $z\in\Gamma(\xi)$.

Set
$$
a_n(\xi)=e^{-1}\bigl(\min e[T_n(\xi)]\bigr),\qquad
b_n(\xi)=e^{-1}\bigl(\max e[T_n(\xi)]\bigr).
$$
Each map is constant on each cell of a finite clopen partition, hence is continuous as a map into $K$. At a fixed $\xi$, the numbers $e(a_n(\xi))$ increase and are bounded above by $e(A_{\min}(\xi))$. Let their limit be $\ell$. A convergent subsequence of $a_n(\xi)$ has limit in every $T_m(\xi)$: all sufficiently late terms lie there, and the set is closed. Thus its limit belongs to $\Gamma(\xi)$ and has $e$-value $\ell$. Minimality gives $\ell\geq e(A_{\min}(\xi))$, proving equality. Continuity of $e^{-1}$ on $e[K]$ now gives convergence of the full sequence to $A_{\min}(\xi)$. For the maximum, $e(b_n(\xi))$ decreases and is bounded below by $e(A_{\max}(\xi))$; the same compact-limit argument places its limiting value in the fiber, where maximality gives the reverse inequality. Hence
$$
a_n(\xi)\longrightarrow A_{\min}(\xi),\qquad
b_n(\xi)\longrightarrow A_{\max}(\xi)
$$
in $K$ at every input. The approximants are continuous digit-space-valued maps, but are not required to be selections at their own inputs.

For completeness, any pointwise limit $f$ of continuous $K$-valued maps $f_n$ is Borel. For a proper nonempty open $O\subset K$, distance to the nonempty closed set $K\setminus O$ gives
$$
f^{-1}(O)=
\bigcup_{k,N\geq1}\ \bigcap_{n\geq N}
\{\xi:d_K(f_n(\xi),K\setminus O)\geq1/k\}.
$$
If $f(\xi)\in O$, its distance to the complement is positive; convergence gives the displayed eventual inequality for a sufficiently large $k$. Conversely, that inequality passes to the limit and excludes membership in the complement. Each inner intersection is closed, so the inverse image is $F_\sigma$. Empty and full open sets give empty and full inverse images. Applying this to $a_n$ and $b_n$ proves Borelness. This construction, rather than an inference from meagre discontinuities or from an ambient real-valued approximation, proves the claimed target-valued Baire class.

**theorem 22.10 (Strict measurable distinctions among selections).** There exist Borel selections that are not of Baire class one. There also exist selections that are not measurable for the completion of a Borel probability measure on $X$, hence are neither Borel nor universally measurable. Nevertheless every point selection is Baire-property measurable. All these selections still have exactly the continuity locus $G$.

**Proof 22.10.** Choose a Cantor set $M$ as in Theorem 22.7, with its constant two-point fiber. Write the two outputs as $z^{(0)},z^{(1)}$, choosing an index $j$ at which $z^{(0)}_j=0$ and $z^{(1)}_j=1$. For any subset $B\subseteq M$, define the selection
$$
A_B(\xi)=
\begin{cases}
z^{(1)},&\xi\in B,\\
z^{(0)},&\xi\in M\setminus B,\\
A_{\min}(\xi),&\xi\notin M.
\end{cases}
$$
Each branch lies in the required fiber, so this is a selection for every $B$, regardless of measurability.

Let $R$ be a countable dense subset of $M$, obtained, for example, by carrying the eventually-zero binary sequences through a homeomorphism onto $M$. The map $A_R$ is Borel: $M$ is closed, $R$ is countable and Borel, and its three pieces use constant maps or the Borel map $A_{\min}$. We first prove that $M\setminus R$ is not $F_\sigma$ in $M$. Otherwise, write it as a countable union of relatively closed sets. Each has empty relative interior because $R$ is dense. Each singleton of $R$ also has empty relative interior because a Cantor space has no isolated points. This would express $M$ as a countable union of relatively closed nowhere dense sets. Such a covering is impossible: transfer it to binary sequence space, successively choose a nonempty cylinder inside the preceding cylinder and disjoint from the next closed nowhere dense set, and require the prescribed prefix lengths to increase. Closedness and empty interior permit each choice. The unique sequence extending all chosen prefixes avoids every member of the proposed covering, a contradiction.

If continuous $K$-valued maps $f_n$ converged pointwise to $A_R$, then on $M$ the continuous real functions $g_n(\xi)=(f_n(\xi))_j$ would converge to the indicator $\mathbf1_R$. Therefore
$$
M\setminus R=\bigcup_{N\geq1}\ \bigcap_{n\geq N}
\{\xi\in M:g_n(\xi)\leq1/4\},
$$
a relatively $F_\sigma$ set. Indeed, a limit of zero eventually satisfies the bound, whereas a limit of one cannot. This contradicts the preceding paragraph and proves that $A_R$ is not Baire one.

For a precise nonmeasurable choice, equip $\mathcal C=\{0,1\}^{\mathbb N}$ with the fair-coin product probability $\mu$. Two sequences are equivalent when they differ in only finitely many coordinates. Choose one representative from each equivalence class and call the representative set $V$. For every finite $s\subseteq\mathbb N$, let $T_s$ flip exactly the coordinates in $s$. The sets $T_s[V]$ are pairwise disjoint and cover $\mathcal C$: two representations of the same point force their representatives to be equivalent and hence equal, and a nonempty finite flip fixes no sequence. There are countably infinitely many finite subsets $s$.

Every $T_s$ preserves $\mu$, since it permutes cylinders of any specified length without changing their measures; uniqueness of the probability measure determined by cylinders gives invariance on Borel sets. It also preserves the completed measure, since it preserves Borel null sets and their subsets. If $V$ were measurable in this completion, all its disjoint translates would have the same measure $t$. For $t=0$, their countable union would have measure zero instead of one. For $t>0$, a sufficiently large finite union would already have measure greater than one. Thus $V$ is not completed-measurable.

Fix a homeomorphism $\psi:\mathcal C\to M$, set $B=\psi[V]$, and let $\nu=\psi_*\mu$, viewed as a Borel probability on $X$ supported on $M$. If $B$ were measurable in the completion of $\nu$, pulling back a Borel representative and its Borel null error would make $V$ measurable in the completion of $\mu$. Hence it is not. Since
$$
M\cap A_B^{-1}(\{z\in K:z_j=1\})=B,
$$
and the digit cylinder is clopen, $A_B$ is not measurable for the completion of $\nu$. In particular it is not Borel or universally measurable. This construction uses choice to select the representatives.

Finally, any selection $A$ agrees with $A_{\min}$ outside the meagre set $D$. Thus for every open $O\subseteq K$, the symmetric difference of $A^{-1}(O)$ and $A_{\min}^{-1}(O)$ is contained in $D$. The latter inverse image is $F_\sigma$ by Theorem 22.9 and has the Baire property: a countable union of closed sets differs from the union of their interiors by a subset of the countable union of their nowhere dense boundaries. Every subset of a meagre set is meagre, because its intersections with the given nowhere dense covering sets are still nowhere dense. This proves the Baire property for $A^{-1}(O)$, even for the nonmeasurable construction above. The common continuity locus follows from Theorem 22.6, not from any of these measurability properties.

**Definition 22.11 (Admissible probability assignments and kernels).** Let $\mathcal P(K)$ be the Borel probability measures on $K$, with the weak topology generated by
$$
\mu\longmapsto\int_K f\,d\mu\qquad(f\in C(K,\mathbb R)).
$$
An admissible probability assignment is any map $P:X\to\mathcal P(K)$ such that
$$
P(\xi)(\Gamma(\xi))=1\qquad(\xi\in X).
$$
This condition expresses support inside the closed fiber. No measurability is included in the word assignment. A Borel probability kernel additionally requires $\xi\mapsto P(\xi)(B)$ to be Borel for every Borel $B\subseteq K$. A Baire-one probability assignment is a pointwise weak limit of continuous maps $X\to\mathcal P(K)$. Write $\delta_z$ for the Dirac probability at $z$.

**theorem 22.12 (Probability outputs have the identical obstruction).** Every admissible probability assignment, measurable or not, satisfies
$$
P(Z(n),Z(m))=\delta_{Z(n+m)},\qquad
\operatorname{Cont}(P)=G.
$$
In particular, no such assignment is globally continuous, or continuous on a nonempty open subspace of $X$.

**Proof 22.12.** A probability giving mass one to a singleton is its Dirac probability, proving the natural-input assertion. If $\Gamma(\xi)=\{z\}$, then $P(\xi)=\delta_z$. Fix a continuous real function $f$ and a positive $\varepsilon$. Choose an open neighborhood $V$ of $z$ such that $|f(w)-f(z)|<\varepsilon/2$ for $w\in V$. Upper semicontinuity of $\Gamma$ gives an input neighborhood on which every fiber lies in $V$. For every input $\eta$ in that neighborhood, support inside its fiber implies
$$
\left|\int_K f\,dP(\eta)-f(z)\right|
\leq\int_K|f-f(z)|\,dP(\eta)\leq\varepsilon/2<\varepsilon.
$$
Intersecting the neighborhoods for finitely many test functions verifies every basic weak neighborhood of $\delta_z$. Thus $P$ is continuous at $\xi$.

If the fiber contains distinct $z_0,z_1$, Theorem 22.4 gives two sequences of actual finite input pairs tending to $\xi$, with their actual sums tending respectively to $z_0,z_1$. Along these sequences $P$ is forced to be the Dirac measure at the actual sum. These probabilities converge weakly to $\delta_{z_0}$ and $\delta_{z_1}$: each test integral is simply the value of its continuous test function at the approaching sum. Choose a digit coordinate $j$ where $z_0$ and $z_1$ differ. The continuous moment $\mu\mapsto\int z_j\,d\mu$ then has two different limiting values along these two input sequences. Continuity at $\xi$ would force both to be its value at $P(\xi)$, a contradiction. This proves the exact locus using approaching actual sums, without an appeal to compactness of the probability space. Density of $D$ and eventual membership of the sequences in any open neighborhood give the remaining assertions.

**theorem 22.13 (Measurable genuine randomization and strict regularity distinctions).** For every constant $\lambda\in[0,1]$, the assignment
$$
P_\lambda(\xi)=(1-\lambda)\delta_{A_{\min}(\xi)}+\lambda\delta_{A_{\max}(\xi)}
$$
is a Borel probability kernel, a Borel map into the weak topology, and Baire one with that target topology. For $0<\lambda<1$, its support is exactly the two-point fiber on $D$. There are also Borel probability kernels that are not weakly Baire one, and admissible assignments that are not measurable for a completed Borel probability on $X$. Nevertheless all admissible probability assignments are Baire-property measurable into the weak topology.

**Proof 22.13.** Both selected atoms belong to the fiber, so the support condition holds. They coincide exactly on $G$ and differ on $D$, proving the support assertion for interior weights. With the continuous $K$-valued approximants of Theorem 22.9, define
$$
P_{\lambda,n}(\xi)=(1-\lambda)\delta_{a_n(\xi)}+\lambda\delta_{b_n(\xi)}.
$$
For each continuous $f$, its integral against this measure is
$$
(1-\lambda)f(a_n(\xi))+\lambda f(b_n(\xi)),
$$
a continuous function of $\xi$. Hence $P_{\lambda,n}$ is weakly continuous. Pointwise convergence of $a_n,b_n$ gives convergence of every test integral to the corresponding integral against $P_\lambda$. This is precisely a same-target weak Baire-one approximation. Support inside the input fiber is required of the limit, not of these continuous approximating maps.

The map $(z,w)\mapsto(1-\lambda)\delta_z+\lambda\delta_w$ is weakly continuous by the same test calculation. The pair $(A_{\min},A_{\max})$ is Borel into $K^2$: a countable base of product cylinders reduces inverse images of open sets to countable unions of intersections of Borel sets. Composition proves weak-topology Borelness of $P_\lambda$. Moreover, for every Borel $B\subseteq K$,
$$
P_\lambda(\xi)(B)=(1-\lambda)\mathbf1_B(A_{\min}(\xi))+
\lambda\mathbf1_B(A_{\max}(\xi))
$$
is Borel, proving the probability-kernel assertion itself.

Use the Borel non-Baire-one selection $A_R$ of Theorem 22.10. Its Dirac assignment is a Borel probability kernel and a weakly Borel map. Suppose it were the pointwise weak limit of continuous maps $Q_n:X\to\mathcal P(K)$. On the same Cantor set $M$, the continuous real functions
$$
g_n(\xi)=\int_K z_j\,dQ_n(\xi)
$$
would tend to $\mathbf1_R$. The eventual $1/4$ bound in Proof 22.10 would again make $M\setminus R$ relatively $F_\sigma$, which was proved impossible. Thus this kernel is not weakly Baire one. For the non-completed-measurable selection $A_B$ there, the same digit moment of $\delta_{A_B}$ restricts on $M$ to $\mathbf1_B$. Its inverse image of $(1/2,\infty)$, intersected with $M$, is $B$. Hence this admissible assignment is not measurable for the completion of the probability $\nu$ constructed there, and in particular is not weakly Borel.

Finally let $P$ be any admissible assignment. Outside $D$ it equals $\delta_{A_{\min}}$. For a weakly open set $O\subseteq\mathcal P(K)$, the set $\{z:\delta_z\in O\}$ is open in $K$, since the Dirac map is weakly continuous. Its inverse image under $A_{\min}$ is $F_\sigma$ by Theorem 22.9. The inverse image $P^{-1}(O)$ differs from that set only inside $D$, so the same meagre-error argument as in Proof 22.10 gives the Baire property. Thus probability-valued continuity and descriptive regularity have the asserted distinct meanings and boundaries.

**theorem 22.14 (Algebraic laws are not consequences of the regularity statements).** The selections $A_{\min}$ and $A_{\max}$, and each constant-weight kernel $P_\lambda$, are commutative. Both of these point selections fail associativity and fail to have $0_K$ as an identity. None of these constant-weight kernels has the Dirac identity law at $0_K$. There also exists a noncommutative Baire-one point selection. Conversely, commutativity alone forces neither Borelness nor Baire class one among selections. All these examples retain exact natural addition and the common continuity locus already proved.

**Proof 22.14.** Swapping the first two coordinates preserves the set of actual finite addition triples. The swap is a homeomorphism, so it preserves its closure. Hence $\Gamma(x,y)=\Gamma(y,x)$. Taking the least or greatest element of the same fiber proves commutativity of both canonical selections. Their constant-weight mixture of Dirac probabilities is commutative as well.

Put $p_2=0v$ and $q_2=10v$. Assumption 22.2, including its specified labels, gives
$$
\Gamma(0_K,u)=\Gamma(0_K,v)=\{u,v\},\qquad
\Gamma(u,u)=\{p_2\},\qquad\Gamma(v,v)=\{q_2\},
$$
$$
\Gamma(0_K,p_2)=\Gamma(0_K,q_2)=\{p_2,q_2\}.
$$
Indeed, $H(0_K)=0\notin E$, so its sign set permits both signs; the other phases in the last display are $[-2\phi]\in E$. The same-sign rule gives the two diagonal singleton fibers. In lexicographic order $v<u$ and $p_2<q_2$, as their first digits show. Consequently
$$
A_{\min}(0_K,u)=v\ne u,\qquad A_{\max}(0_K,v)=u\ne v,
$$
so the proposed identity fails. Furthermore,
$$
A_{\min}(A_{\min}(0_K,v),v)=q_2\ne p_2
=A_{\min}(0_K,A_{\min}(v,v)),
$$
$$
A_{\max}(A_{\max}(0_K,u),u)=p_2\ne q_2
=A_{\max}(0_K,A_{\max}(u,u)).
$$
These are explicit failures of associativity for the two named selections. For the probability kernels,
$$
P_\lambda(0_K,u)=P_\lambda(0_K,v)=(1-\lambda)\delta_v+\lambda\delta_u.
$$
The identity requirement at $u$ would force $\lambda=1$, whereas the one at $v$ would force $\lambda=0$. Thus no constant weight gives the Dirac identity law.

For a noncommutative Baire-one example, change $A_{\min}$ only at $\xi_*=(0_K,u)$, assigning $u$ there, and denote the result by $A_*$. It remains a selection. At the transposed input $(u,0_K)$ it still equals $v$, so it is not commutative. For the nested clopen cells $C_n(\xi_*)$ used in Theorem 22.9, define a map equal to the constant $u$ on that cell and equal to $a_n$ outside it. Each such map is continuous into $K$. At $\xi_*$ it converges to $u$. At any other input it eventually equals $a_n$, because the cells shrink to the singleton $\{\xi_*\}$. Its limit there is $A_{\min}$. These maps prove that $A_*$ is Baire one.

To separate commutativity from the other regularities, take disjoint nonempty clopen cylinders $U,V\subset K$ and obtain the Cantor set $M\subset U\times V$ from Theorem 22.7. Its transpose $\tau M\subset V\times U$ is disjoint from $M$. Make either construction $A_R$ or $A_B$ from Theorem 22.10 on $M$, make the identical choices at transposed points in $\tau M$, and retain $A_{\min}$ elsewhere. Symmetry of the relation makes this a commutative selection. In the $R$ case it is Borel, since both modified sets are closed with countable distinguished subsets, but its restriction to $M$ retains the proof of failure of Baire class one. In the $B$ case its restriction to $M$ retains the failure of completed measurability for the probability supported there. Thus commutativity supplies neither missing regularity. The natural input fibers remain singleton fibers in all cases, so none of the modifications can change natural addition. Their continuity loci follow from Theorem 22.6.

These counterexamples establish the stated nonimplications, not a classification of associative selections. In particular, the existence or nonexistence of other associative selections, and any separately defined associativity law for composed probability kernels, are not asserted here. The exact continuity obstruction, the descriptive loci, and the constructions in Theorems 22.6–22.13 require no such law.

## 追加锚（本行以下为增补区）
## 23. Zeckendorf 加法闭图的概率结合律刚性

**定义 23.0（固定数字载体与相位）。** 取 $\mathbb N=\{0,1,2,\ldots\}$，置
$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,\qquad
\phi=\frac{1+\sqrt5}{2},\qquad \alpha=\phi^{-1}.
$$
令 $Z(n)$ 为以 $G_j$ 为权的有限 Zeckendorf 规范字按低位到高位补零后的无限字，并令
$$
K=\{x\in\{0,1\}^{\mathbb N}:\forall j,\ x_jx_{j+1}=0\},\qquad 0_K=Z(0).
$$
载体取数字乘积拓扑。定义
$$
\mathbb T=\mathbb R/\mathbb Z,\qquad
F(x)=\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j,\qquad H(x)=[F(x)],
$$
$$
E_m=[-m\phi]\quad(m\ge1),\qquad E=\{E_m:m\ge1\},
$$
以及
$$
\Gamma=\overline{\{(Z(n),Z(m),Z(n+m)):n,m\in\mathbb N\}}^{\,K^3},
\qquad
\Gamma(x,y)=\{w:(x,y,w)\in\Gamma\}.
$$
这些记号采用[本卷定义16.0的固定文本](https://raw.githubusercontent.com/the-omega-institute/trureturing/c74985438ae17d205509255934bbd3ecf1f94d71/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)。

**假设 23.1（完整纤维与精确支撑契约）。** 本节明确采用以下相位纤维及关系公式。映射 $H:K\to\mathbb T$ 满射；对 $\theta\in E$，
$$
H^{-1}(\{\theta\})=\{z_\theta^{+1},z_\theta^{-1}\},
\qquad z_\theta^{+1}\ne z_\theta^{-1};
$$
对 $\theta\notin E$，该纤维只有一点，记为 $k_\theta$。另有
$$
H^{-1}(\{[n\phi]\})=\{Z(n)\}\quad(n\in\mathbb N),
\qquad k_0=0_K.
$$
正负标记固定采用定义16.3的定向标记。置
$$
\mathcal S(x)=
\begin{cases}
\{\sigma\},&H(x)\in E,\ x=z_{H(x)}^\sigma,\quad \sigma\in\{-1,+1\},\\
\{-1,+1\},&H(x)\notin E.
\end{cases}
$$
对全部 $x,y\in K$，以 $\lambda=H(x)+H(y)$ 记输出相位，假设
$$
\Gamma(x,y)=
\begin{cases}
\{k_\lambda\},&\lambda\notin E,\\
\{z_\lambda^\sigma:\sigma\in\mathcal S(x)\cup\mathcal S(y)\},&\lambda\in E.
\end{cases}
$$
特别地，两个同号分裂输入只能产生同号输出；任何非分裂输入在分裂输出处允许两个符号。这里采用的是完整输入纤维公式，而不只是输出相位相加。相位前提见[Zeckendorf 理论卷第371—372节，尤其定理372.2—372.4](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)；定向标记及关系公式见[本卷定义16.3、定理16.4](https://raw.githubusercontent.com/the-omega-institute/trureturing/c74985438ae17d205509255934bbd3ecf1f94d71/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)。

**定义 23.2（有限概率核与结合律）。** 对任意集合 $X$，定义
$$
\mathcal D_f(X)=
\left\{\mu:X\to[0,1]:
\operatorname{supp}\mu=\{x:\mu(x)>0\}\text{ 有限},
\ \sum_{x\in\operatorname{supp}\mu}\mu(x)=1\right\}.
$$
记 $\delta_x$ 为集中在 $x$ 的分布，$\mu(x)$ 也记为 $\mu\{x\}$。一个可容许概率核是任意函数
$$
P:K\times K\to\mathcal D_f(K),\qquad
\operatorname{supp}P_{x,y}\subseteq\Gamma(x,y).
$$
允许一个许可输出的质量为零；不预设连续性、Borel 可测性、交换律或单位律。相对于 $P$，定义有限卷积
$$
\mu*\nu=
\sum_{x\in\operatorname{supp}\mu}
\sum_{y\in\operatorname{supp}\nu}
\mu(x)\nu(y)P_{x,y}.
$$
称 $P$ 结合，若对所有 $x,y,z\in K$，
$$
\sum_{u\in\operatorname{supp}P_{x,y}}P_{x,y}(u)P_{u,z}
=
\sum_{v\in\operatorname{supp}P_{y,z}}P_{y,z}(v)P_{x,v}.
$$
等号是分布逐点相等，而非支撑集合相等。这里的有限凸组合与展平采用有限分布单子的通常含义，其单位和展平分别为
$$
\eta_X(x)=\delta_x,\qquad
m_X\left(\sum_i a_i\delta_{\mu_i}\right)=\sum_i a_i\mu_i.
$$
此处单子的单位是映射 $\eta_X$，不是二元操作 $P$ 的单位元。相关定义见 Bart Jacobs，*Duality for Convexity*，[arXiv:0911.3834，§2，Example 2(3)—(4)，PDF第3—4页](https://arxiv.org/pdf/0911.3834)。

**定理 23.3（有限卷积的闭合与结合延拓）。** 定义23.2的卷积总是属于 $\mathcal D_f(K)$。可容许核的点态结合律等价于 $\mathcal D_f(K)$ 上全部有限分布的结合律。每个 $P_{x,y}$ 都集中在相位 $H(x)+H(y)$；若 $\Gamma(x,y)=\{w\}$，则 $P_{x,y}=\delta_w$。

**证明。** 卷积的支撑包含在有限集合
$$
\bigcup_{\substack{x\in\operatorname{supp}\mu\\y\in\operatorname{supp}\nu}}
\operatorname{supp}P_{x,y}
$$
中，其大小至多为 $2|\operatorname{supp}\mu|\,|\operatorname{supp}\nu|$。各质量非负，总质量为
$$
\sum_{x,y}\mu(x)\nu(y)\sum_w P_{x,y}(w)
=\sum_{x,y}\mu(x)\nu(y)=1.
$$
以上及以下求和都限制在相应有限支撑中。

若点态结合律成立，把三个有限分布的卷积展开，得到
$$
(\mu*\nu)*\xi
=\sum_{x,y,z}\mu(x)\nu(y)\xi(z)\bigl(P_{x,y}*\delta_z\bigr),
$$
$$
\mu*(\nu*\xi)
=\sum_{x,y,z}\mu(x)\nu(y)\xi(z)\bigl(\delta_x*P_{y,z}\bigr).
$$
点态结合律使每个相应括号相等，故两式相等。反向取三个 Dirac 分布即可。假设23.1给出全部许可输出的同一相位；支撑包含关系将此性质传给 $P$。支撑包含于单点而总质量为一时，该点质量只能为一。证毕。

**定理 23.4（分裂相位的加法与半周平移）。** 分裂相位满足
$$
E_m=E_n\Longleftrightarrow m=n,\qquad E_m+E_n=E_{m+n},
\qquad [k\phi]\notin E\quad(k\in\mathbb N).
$$
置 $\tau=[1/2]$，则
$$
\tau\notin E,\qquad (E+\tau)\cap E=\varnothing.
$$
因而存在唯一 $t=k_\tau\in K$。对任意可容许核，
$$
P_{t,t}=\delta_{0_K},
\qquad
P_{t,x}=P_{x,t}=\delta_{k_{\theta+\tau}}
\quad\text{当 }H(x)=\theta\in E.
$$

**证明。** $\phi$ 无理。相位相等 $E_m=E_n$ 意味着 $(m-n)\phi$ 为整数，故 $m=n$；相位加法公式直接成立。若 $[k\phi]=E_m$，则 $(k+m)\phi$ 为整数，其中 $k+m>0$，矛盾。

若 $\tau=E_m$，则 $m\phi$ 为半整数，亦矛盾。若 $E_m+\tau=E_n$，则 $(n-m)\phi+1/2$ 为整数；当 $n=m$ 时不可能，当 $n\ne m$ 时又迫使 $\phi$ 有理。所以两集合不交。假设23.1保证半周相位有唯一原像，而 $2\tau=0$ 的原像为 $0_K$。当 $\theta\in E$ 时，$\theta+\tau$ 非分裂，故两个有序乘积的许可纤维是同一单点。定理23.3遂给所列 Dirac 等式，不需要预设交换律。证毕。

**定理 23.5（零切片下降与双侧平均恒等式）。** 设 $P$ 可容许且结合。则存在唯一一族 $\pi_\theta\in\mathcal D_f(K)$，使
$$
P_{0_K,x}=P_{x,0_K}=\pi_{H(x)}
\quad(x\in K).
$$
每个 $\pi_\theta$ 支撑于 $H^{-1}(\{\theta\})$，且 $\pi_0=\delta_{0_K}$。对所有 $\theta,\rho\in\mathbb T$ 和 $x,y\in K$，
$$
\pi_\theta*\delta_y=\pi_{\theta+H(y)},\qquad
\delta_x*\pi_\rho=\pi_{H(x)+\rho},\qquad
\pi_\theta*\pi_\rho=\pi_{\theta+\rho}.
$$

**证明。** 先分别证明左、右零切片仅依赖相位。非分裂相位的输出纤维只有一个点，所以两个零切片均为 $\delta_{k_\theta}$。对分裂相位 $\theta$，置 $w_\theta=k_{\theta+\tau}$。任取 $H(x)=\theta$，在两个不同有序三元组上使用结合律及定理23.4，得到
$$
\delta_{0_K}*\delta_x
=(\delta_t*\delta_t)*\delta_x
=\delta_t*(\delta_t*\delta_x)
=P_{t,w_\theta},
$$
$$
\delta_x*\delta_{0_K}
=\delta_x*(\delta_t*\delta_t)
=(\delta_x*\delta_t)*\delta_t
=P_{w_\theta,t}.
$$
右端均与该纤维内的输入分支无关。于是左、右零切片分别定义为 $L_\theta,R_\theta$，暂不假设二者相等。它们均支撑于相位 $\theta$。

对三元组 $(0_K,x,0_K)$ 使用结合律。左括号给出
$$
L_\theta*\delta_{0_K}
=\sum_{u\in\operatorname{supp}L_\theta}L_\theta(u)R_\theta
=R_\theta,
$$
右括号给出
$$
\delta_{0_K}*R_\theta
=\sum_{v\in\operatorname{supp}R_\theta}R_\theta(v)L_\theta
=L_\theta.
$$
故 $L_\theta=R_\theta$，记为 $\pi_\theta$。满射性保证这族分布在全部相位上定义且唯一；零相位的单点纤维给 $\pi_0=\delta_{0_K}$。

固定 $\theta$，由满射性取 $H(x)=\theta$。若 $H(y)=\rho$，则
$$
\pi_\theta*\delta_y
=(\delta_{0_K}*\delta_x)*\delta_y
=\delta_{0_K}*P_{x,y}
=\sum_u P_{x,y}(u)\pi_{\theta+\rho}
=\pi_{\theta+\rho}.
$$
这里每个中间点 $u$ 都具有相位 $\theta+\rho$。同理，
$$
\delta_x*\pi_\rho
=\delta_x*(\delta_y*\delta_{0_K})
=P_{x,y}*\delta_{0_K}
=\sum_u P_{x,y}(u)\pi_{\theta+\rho}
=\pi_{\theta+\rho}.
$$
最后，$\pi_\rho$ 的每个支撑点具有相位 $\rho$，故再对第一式作有限平均，得到 $\pi_\theta*\pi_\rho=\pi_{\theta+\rho}$。全程没有使用 $0_K$ 是单位元。证毕。

**定理 23.6（单个分裂相位的零切片必为 Dirac 分布）。** 设 $P$ 可容许且结合。固定 $m\ge1$，记
$$
x_+=z_{E_m}^{+1},\quad x_-=z_{E_m}^{-1},\qquad
y_+=z_{E_{2m}}^{+1},\quad y_-=z_{E_{2m}}^{-1},
$$
并定义
$$
p=\pi_{E_m}(x_+),\qquad q=\pi_{E_{2m}}(y_+),\qquad
a=P_{x_+,x_-}(y_+),\qquad b=P_{x_-,x_+}(y_+).
$$
则以下两个恒等链同时成立：
$$
q=p+(1-p)b=pa,\qquad
q=p+(1-p)a=pb.
$$
它们强制
$$
p=q=a=b\in\{0,1\}.
$$
特别地，每个 $\pi_{E_m}$ 都是 Dirac 分布。

**证明。** 精确支撑契约给出
$$
P_{x_+,x_+}=\delta_{y_+},\qquad
P_{x_-,x_-}=\delta_{y_-},
\qquad
\pi_{E_m}=p\delta_{x_+}+(1-p)\delta_{x_-}.
$$
定理23.5分别对
$$
\pi_{E_m}*\delta_{x_+},\quad
\delta_{x_+}*\pi_{E_m},\quad
\pi_{E_m}*\delta_{x_-},\quad
\delta_{x_-}*\pi_{E_m}
$$
给出同一分布 $\pi_{E_{2m}}$。读取 $y_+$ 的质量，依次得到
$$
q=p+(1-p)b,\qquad q=p+(1-p)a,\qquad q=pa,\qquad q=pb.
$$
这证明两个恒等链，且没有把两个有序混合乘积预先等同。

由 $0\le a,b,p\le1$，第一式给 $q\ge p$，第三式给 $q\le p$，所以 $q=p$。代回四式可得
$$
(1-p)b=0,\qquad (1-p)a=0,\qquad
p(1-a)=0,\qquad p(1-b)=0.
$$
若 $0<p<1$，则 $(1-p)a=0$ 强制 $a=0$，而 $p(1-a)=0$ 强制 $a=1$，矛盾。因此 $p$ 只能是零或一。

当 $p=0$ 时，$q=p=0$，前两条零乘积式给 $a=b=0$。当 $p=1$ 时，$q=p=1$，后两条零乘积式给 $a=b=1$。两个端点均已单独处理，没有除以可能为零的质量。两点纤维上的分布由 $p$ 完全确定，故必为 Dirac 分布。证毕。

**定理 23.7（所有分裂相位共享一个符号）。** 对任意可容许结合核，存在唯一 $s\in\{-1,+1\}$，使
$$
\pi_{E_m}=\delta_{z_{E_m}^{s}}\qquad(m\ge1).
$$

**证明。** 定理23.6允许唯一写作 $\pi_{E_m}=\delta_{z_{E_m}^{\sigma_m}}$，其中 $\sigma_m\in\{-1,+1\}$。固定任意 $m,n\ge1$，取 $v_n=z_{E_n}^{\sigma_m}$。定理23.5和同号强制支撑共同给出
$$
\pi_{E_{m+n}}
=\pi_{E_m}*\delta_{v_n}
=P_{z_{E_m}^{\sigma_m},z_{E_n}^{\sigma_m}}
=\delta_{z_{E_{m+n}}^{\sigma_m}}.
$$
再取 $v_m=z_{E_m}^{\sigma_n}$，在另一个有序位置使用平均恒等式：
$$
\pi_{E_{m+n}}
=\delta_{v_m}*\pi_{E_n}
=P_{z_{E_m}^{\sigma_n},z_{E_n}^{\sigma_n}}
=\delta_{z_{E_{m+n}}^{\sigma_n}}.
$$
输出纤维的两个标记互异，故
$$
\sigma_m=\sigma_{m+n}=\sigma_n.
$$
由于 $m,n$ 任意，所有符号相同。以 $\pi_{E_1}$ 确定的符号为 $s$，同时得到存在性和唯一性。证毕。

**定义 23.8（两个固定符号操作）。** 对固定 $s\in\{-1,+1\}$，定义
$$
c_s(\theta)=
\begin{cases}
z_\theta^s,&\theta\in E,\\
k_\theta,&\theta\notin E,
\end{cases}
\qquad
R_s=c_s[\mathbb T],\qquad
N_s=\{z_{E_m}^{-s}:m\ge1\}.
$$
假设23.1给出 $K=R_s\sqcup N_s$。定义
$$
A_s(x,y)=
\begin{cases}
z_{H(x)+H(y)}^{-s},&x,y\in N_s,\\
c_s(H(x)+H(y)),&\text{其余情形},
\end{cases}
\qquad P^s_{x,y}=\delta_{A_s(x,y)}.
$$
第一分支由 $E+E\subseteq E$ 保证有定义。等价地，两个分裂输入都具有符号 $-s$ 时保留强制符号 $-s$；其余分裂输出一律取符号 $s$，非分裂输出取其唯一原像。

**定理 23.9（全载体概率结合核的完整分类）。** 在假设23.1下，对任意可容许概率核 $P$，
$$
P\text{ 结合}
\quad\Longleftrightarrow\quad
\exists!\,s\in\{-1,+1\}\ \forall x,y\in K,\quad P_{x,y}=P^s_{x,y}.
$$
因此恰有两个解，每个解逐点为 Dirac 分布，并自动满足交换律。它们包含如下全域边界公式：
$$
P^s_{0_K,x}=P^s_{x,0_K}=\delta_{c_s(H(x))},
$$
$$
P^s_{z_{E_m}^{+1},z_{E_n}^{-1}}
=P^s_{z_{E_m}^{-1},z_{E_n}^{+1}}
=\delta_{z_{E_{m+n}}^s}\qquad(m,n\ge1),
$$
$$
P^s_{Z(n),Z(m)}=\delta_{Z(n+m)}\qquad(n,m\in\mathbb N).
$$
若进一步要求全部许可输出都有严格正质量，即对所有输入都有 $\operatorname{supp}P_{x,y}=\Gamma(x,y)$，则不存在结合解。

**证明。** 先证明必要性。由定理23.5—23.7及非分裂纤维的唯一性，存在唯一符号 $s$，使
$$
\pi_\theta=\delta_{c_s(\theta)}\qquad(\theta\in\mathbb T).
$$
取任意有序输入对 $(x,y)$。若 $x\in R_s$，则 $\delta_x=\pi_{H(x)}$，所以平均恒等式给
$$
P_{x,y}=\pi_{H(x)}*\delta_y
=\delta_{c_s(H(x)+H(y))}.
$$
若 $y\in R_s$，则另一个平均恒等式同样给
$$
P_{x,y}=\delta_x*\pi_{H(y)}
=\delta_{c_s(H(x)+H(y))}.
$$
剩下的唯一情形是 $x,y\in N_s$。此时两输入都是符号 $-s$ 的分裂点，假设23.1直接强制
$$
P_{x,y}=\delta_{z_{H(x)+H(y)}^{-s}}.
$$
这正是定义23.8，覆盖非分裂输入、零、分裂输入的两种顺序以及所有相位和；没有预设确定性选择的分类。

再证明两个候选确实存在。若 $x,y\in N_s$，定义选取的点就是同号强制输出。否则，当输出相位分裂时，至少一个输入非分裂或具有符号 $s$，所以 $s\in\mathcal S(x)\cup\mathcal S(y)$，所选点属于 $\Gamma(x,y)$；当输出相位非分裂时，所选点是唯一许可输出。因此每个 $P^s$ 都可容许。

为验证所有三元组的结合律，定义
$$
\varepsilon_s(x)=
\begin{cases}
1,&x\in N_s,\\
0,&x\in R_s,
\end{cases}
\qquad
M=(\mathbb T\times\{0\})\cup(E\times\{1\}),
$$
并在 $M$ 上定义
$$
(\theta,i)\cdot(\rho,j)=(\theta+\rho,ij).
$$
若 $ij=1$，两个相位均属于 $E$，故其和仍属于 $E$；若 $ij=0$，输出属于 $\mathbb T\times\{0\}$。所以该乘法封闭。它的结合性和交换性分别来自圆周加法及 $\{0,1\}$ 上通常乘法的结合性和交换性。

映射
$$
\Phi_s:K\to M,\qquad \Phi_s(x)=(H(x),\varepsilon_s(x))
$$
是双射：$(\theta,0)$ 的唯一原像是 $c_s(\theta)$，而对 $\theta\in E$，$(\theta,1)$ 的唯一原像是 $z_\theta^{-s}$。定义23.8逐分支给出
$$
\Phi_s(A_s(x,y))=\Phi_s(x)\cdot\Phi_s(y).
$$
因而两个括号的像均为
$$
\bigl(H(x)+H(y)+H(z),\,
\varepsilon_s(x)\varepsilon_s(y)\varepsilon_s(z)\bigr).
$$
由 $\Phi_s$ 单射，$A_s(A_s(x,y),z)=A_s(x,A_s(y,z))$。交换律同理成立。于是相应 Dirac 核满足点态结合律，定理23.3又给全部有限分布上的结合律。

两个核在 $(0_K,z_{E_1}^{+1})$ 处分别输出 $z_{E_1}^{+1}$ 和 $z_{E_1}^{-1}$，故互异。必要性中的全局符号唯一，排除了任何第三个核。零切片公式由 $0_K\in R_s$ 得到；每个异号输入对恰有一个输入属于 $R_s$，给出两个有序混合公式。核心相位之和为 $[(n+m)\phi]$，其唯一原像为 $Z(n+m)$，给出核心公式。最后，$\Gamma(0_K,z_{E_1}^{+1})$ 有两个点，而每个结合解在该处只有一个正质量点，所以严格全支撑条件不可能成立。证毕。

**定理 23.10（内部群、全载体无单位与超群公理障碍）。** 对每个 $s$，$R_s$ 是 $(K,A_s)$ 的双侧理想，且其内部运算使 $c_s$ 成为从圆周加法群到 $R_s$ 的抽象群同构；内部单位为 $0_K$。子半群 $N_s$ 与正整数加法半群同构。但 $(K,A_s)$ 没有左单位，也没有右单位。更一般地，任何满足假设23.1支撑契约的概率核，都不能成为全载体 $K$ 上的 DJS 超群卷积。这里使用的标准超群单位及对合支撑公理见 László Székelyhidi，*Functional Equations on Hypergroups*，[§1，公理(H3)—(H4)及(D3)—(D4)，作者提供的PDF第1—3页](https://szekelyhidilaszlo.webzenit.hu/wp-content/uploads/2014/05/Functional-equations-on-hypergroups-styled.pdf)。

**证明。** 只要一个输入在 $R_s$ 中，输出就是 $c_s(H(x)+H(y))\in R_s$，故 $R_s$ 为双侧理想。又有
$$
A_s(c_s(\theta),c_s(\rho))=c_s(\theta+\rho),\qquad
c_s(0)=0_K,\qquad
A_s(c_s(\theta),c_s(-\theta))=0_K.
$$
$Hc_s$ 为恒等映射，而 $c_s$ 按定义满到 $R_s$，所以这给出所述抽象群同构。另一方面，
$$
A_s(z_{E_m}^{-s},z_{E_n}^{-s})=z_{E_{m+n}}^{-s},
$$
而相位指标互异，故 $m\mapsto z_{E_m}^{-s}$ 给正整数加法半群到 $N_s$ 的同构。

若 $e$ 是全载体上的左单位，则 $A_s(e,0_K)=0_K$；读取相位得到 $H(e)=0$，所以 $e=0_K$。然而
$$
A_s(0_K,z_{E_1}^{-s})=z_{E_1}^s\ne z_{E_1}^{-s}.
$$
这排除左单位。右单位同样先被迫为 $0_K$，再由右零切片公式排除。

最后，标准 DJS 超群公理特别要求存在单位 $e$ 和对合 $\iota$，满足
$$
P_{e,x}=P_{x,e}=\delta_x,\qquad
\iota^2=\operatorname{id},\qquad
e\in\operatorname{supp}P_{x,y}\Longleftrightarrow y=\iota(x).
$$
最后一式是通常对合支撑公理的等价写法。单位律在 $(e,0_K)$ 处与相位契约共同迫使 $e=0_K$。固定任意 $m\ge1$，取 $r_m=Z(m)$。由于 $H(r_m)+E_m=0$ 且零相位只有一个原像，
$$
P_{r_m,z_{E_m}^{+1}}=P_{r_m,z_{E_m}^{-1}}=\delta_{0_K}.
$$
对合支撑公理因而同时要求
$$
z_{E_m}^{+1}=\iota(r_m)=z_{E_m}^{-1},
$$
与分裂纤维的两点互异矛盾。这个障碍已经发生在单位和对合支撑公理上，无需诉诸任何拓扑或可测性条件。证毕。

**定理 23.11（许可关系本身的结合律）。** 假设23.1下，集合值关系确实满足
$$
\bigcup_{u\in\Gamma(x,y)}\Gamma(u,z)
=
\bigcup_{v\in\Gamma(y,z)}\Gamma(x,v)
\qquad(x,y,z\in K).
$$
更准确地，令 $\lambda=H(x)+H(y)+H(z)$，共同值为
$$
\begin{cases}
\{k_\lambda\},&\lambda\notin E,\\
\{z_\lambda^\sigma:
\sigma\in\mathcal S(x)\cup\mathcal S(y)\cup\mathcal S(z)\},
&\lambda\in E.
\end{cases}
$$

**证明。** 先证明对每个输入对都有
$$
\bigcup_{u\in\Gamma(x,y)}\mathcal S(u)
=\mathcal S(x)\cup\mathcal S(y).
$$
若 $H(x)+H(y)\in E$，许可输出恰按右侧符号逐个列出，而每个分裂输出的符号集为单点，所以等式成立。若相位和不在 $E$，唯一输出非分裂，左侧为 $\{-1,+1\}$。此时两输入不可能都分裂，因为 $E+E\subseteq E$；至少一个输入非分裂，故右侧也为 $\{-1,+1\}$。

若最终相位 $\lambda$ 非分裂，两个括号中的每个最终输出均为 $k_\lambda$；中间许可纤维非空，故两边确为该单点集。若 $\lambda$ 分裂，则左括号允许的符号集合是
$$
\bigcup_{u\in\Gamma(x,y)}
\bigl(\mathcal S(u)\cup\mathcal S(z)\bigr)
=\mathcal S(x)\cup\mathcal S(y)\cup\mathcal S(z).
$$
右括号用同一恒等式得到完全相同的符号集合。两点纤维的标记唯一确定输出，结论成立。证毕。

**定理 23.12（常偏置权重的精确结合缺陷）。** 对 $r\in[0,1]$，定义
$$
B^{(r)}_{x,y}=rP^{+1}_{x,y}+(1-r)P^{-1}_{x,y},
$$
并以 $*_r$ 表示其有限卷积。这是可容许核；在许可纤维只有一点时取该 Dirac 分布，在许可纤维有两点时，正、负标记的质量分别为 $r,1-r$。它结合当且仅当 $r\in\{0,1\}$。

更具体地，固定任意 $m\ge1$，取 $x_+=z_{E_m}^{+1}$ 和 $y_\pm=z_{E_{2m}}^{\pm1}$，则
$$
(\delta_{0_K}*_r\delta_{x_+})*_r\delta_{x_+}
=(2r-r^2)\delta_{y_+}+(1-r)^2\delta_{y_-},
$$
$$
\delta_{0_K}*_r(\delta_{x_+}*_r\delta_{x_+})
=r\delta_{y_+}+(1-r)\delta_{y_-}.
$$
特别地，对许可双点纤维赋等概率的核，在三元组 $(0_K,z_{E_1}^{+1},z_{E_1}^{+1})$ 上给出不同结果：
$$
\frac34\delta_{z_{E_2}^{+1}}+\frac14\delta_{z_{E_2}^{-1}}
\ne
\frac12\delta_{z_{E_2}^{+1}}+\frac12\delta_{z_{E_2}^{-1}}.
$$

**证明。** 两个候选均可容许，故其凸组合仍可容许。若许可纤维是单点，两候选都取该点；若许可纤维有两点，两输入不是同号分裂输入，故 $A_{+1}$ 取正号而 $A_{-1}$ 取负号，得到所述权重。

另记 $x_-=z_{E_m}^{-1}$。由定义，
$$
B^{(r)}_{0_K,x_+}=r\delta_{x_+}+(1-r)\delta_{x_-},
\qquad B^{(r)}_{x_+,x_+}=\delta_{y_+},
$$
$$
B^{(r)}_{x_-,x_+}=r\delta_{y_+}+(1-r)\delta_{y_-},
\qquad
B^{(r)}_{0_K,y_+}=r\delta_{y_+}+(1-r)\delta_{y_-}.
$$
对第一层有限分布逐项卷积，左括号为
$$
r\delta_{y_+}
+(1-r)\bigl(r\delta_{y_+}+(1-r)\delta_{y_-}\bigr),
$$
右括号为 $B^{(r)}_{0_K,y_+}$，即得两个公式。它们在正标记处的质量差是 $r(1-r)$，故每个 $0<r<1$ 都不结合。两个端点分别为定理23.9已证明结合的 $P^{-1}$ 与 $P^{+1}$。取 $r=1/2,m=1$ 得到所列等概率反例。证毕。

**定理 23.13（仅保留相位兼容时的随机边界）。** 若把精确支撑契约放宽为
$$
\operatorname{supp}Q_{x,y}\subseteq
H^{-1}(\{H(x)+H(y)\}),
$$
则存在真正非 Dirac 的结合概率核。更一般地，任给一族
$$
\eta_\theta\in\mathcal D_f(K),\qquad
\operatorname{supp}\eta_\theta\subseteq H^{-1}(\{\theta\}),
$$
公式 $Q_{x,y}=\eta_{H(x)+H(y)}$ 总定义一个相位兼容的结合核。

**证明。** 固定 $x,y,z$。每个 $u\in\operatorname{supp}Q_{x,y}$ 都有 $H(u)=H(x)+H(y)$，所以
$$
\sum_u Q_{x,y}(u)Q_{u,z}
=\sum_u Q_{x,y}(u)\eta_{H(x)+H(y)+H(z)}
=\eta_{H(x)+H(y)+H(z)}.
$$
对右括号作同样的有限求和，得到同一分布，因此结合。取
$$
\eta_\theta=
\begin{cases}
\frac12\delta_{z_\theta^{+1}}+\frac12\delta_{z_\theta^{-1}},
&\theta\in E,\\
\delta_{k_\theta},&\theta\notin E
\end{cases}
$$
即得非 Dirac 实例。但是对 $x=y=z_{E_m}^{+1}$，
$$
Q_{x,y}=\frac12\delta_{z_{E_{2m}}^{+1}}
+\frac12\delta_{z_{E_{2m}}^{-1}},
\qquad
\Gamma(x,y)=\{z_{E_{2m}}^{+1}\}.
$$
它给被精确关系排除的负标记赋予正质量，故不满足假设23.1的支撑契约，也不是定理23.9的反例。证毕。

## 追加锚（本行以下为增补区）
## 24. Sharp Zeckendorf translation precision and prefix-ultrametric sensitivity

**Definition 24.1 (Standing assumptions, carrier, and observation budget).** All indices and translation parameters belong to $\mathbb N_0=\{0,1,2,\ldots\}$. Fix
$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,\qquad
\phi=\frac{1+\sqrt5}{2},\qquad \alpha=\phi^{-1},\qquad \lambda=-\alpha.
$$
The carrier and its finite observations are
$$
K=\{x\in\{0,1\}^{\mathbb N_0}:x_jx_{j+1}=0\text{ for every }j\},\qquad
q_L(x)=(x_0,\ldots,x_{L-1}),\qquad X_L=q_L[K].
$$
Here $q_0$ has the unique value $\varnothing$, and digits are ordered from low to high. For $p\in X_L$, put
$$
V_L(p)=\sum_{j<L}G_jp_j,\qquad C_p=q_L^{-1}(\{p\}).
$$
Write $Z(n)$ for the zero-padded legal Zeckendorf expansion of $n$. Give $K$ the subspace topology of the product of discrete digit spaces. If $x$ has an actual adjacent pair $00$, let $j$ be its first position and define
$$
(Tx)_i=\begin{cases}
0,&i<j,\\
1,&i=j,\\
x_i,&i>j.
\end{cases}
$$
If there is no adjacent $00$, set $Tx=Z(0)$. Thus the two alternating points $u=(10)^\infty$ and $v=(01)^\infty$ both map to $Z(0)$. No inverse of $T$ is assumed. Define
$$
F(x)=\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j,\qquad
H(x)=[F(x)]\in\mathbb T=\mathbb R/\mathbb Z,\qquad e_s=[-s\phi]\quad(s\ge1).
$$
The circle is oriented by increasing real coordinates. All subsequent fibre conditions quantify over the whole carrier $K$, including its non-eventually-zero points. Set
$$
\mu_k(L)=\min\{m\in\mathbb N_0:\forall x,y\in K,\ q_m(x)=q_m(y)\Longrightarrow q_L(T^kx)=q_L(T^ky)\},
$$
with $\min\varnothing=+\infty$ until finiteness is proved. The carrier, phase, and successor conventions are those of [Z: `CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md`, Sections 371-375, revision `c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb`](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md). The actual-image factorization convention is [R: `RECURSIVE_RELATIONAL_OBSERVATION.md`, Definition 2.1 and theorem 2.2, revision `c74985438ae17d205509255934bbd3ecf1f94d71`](https://raw.githubusercontent.com/the-omega-institute/trureturing/c74985438ae17d205509255934bbd3ecf1f94d71/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md).

**theorem 24.2 (Exact uniform precision and finite sharpness).** For every $k\ge0$, $\mu_k(0)=0$. For every $k\ge0$, $L\ge1$, and $m\ge0$, the following are equivalent:
$$
\forall x,y\in K,\quad q_m(x)=q_m(y)\Longrightarrow q_L(T^kx)=q_L(T^ky);
$$
$$
\exists!\,f_{k,L,m}:X_m\longrightarrow X_L,\qquad q_L\circ T^k=f_{k,L,m}\circ q_m;
$$
$$
G_m\ge G_L+k.
$$
The same criterion holds if the fibre implication is required only for $x=Z(a)$ and $y=Z(b)$ with $a,b\in\mathbb N_0$. Whenever the factor exists, it is
$$
f_{k,L,m}(p)=q_L\bigl(Z(V_m(p)+k)\bigr).
$$
Consequently,
$$
\boxed{\ \mu_k(L)=\min\{m\ge0:G_m\ge G_L+k\}\quad(L\ge1).\ }
$$
For $J=\mu_k(L)$, there are distinct nonnegative integers $a,b<G_{L+k}$ such that $Z(a)$ and $Z(b)$ first differ at position $J-1$, whereas $Z(a+k)$ and $Z(b+k)$ first differ at position $L-1$. In particular these same integers refute every input depth $m<J$.

All Fibonacci threshold equalities belong to the sufficient side: for $L\ge1$ and $m\ge1$,
$$
\mu_k(L)=m\quad\Longleftrightarrow\quad G_{m-1}<G_L+k\le G_m.
$$
In particular,
$$
\mu_0(L)=L,\qquad \mu_1(L)=L+1,\qquad L\le\mu_k(L)\le L+k\qquad(L\ge1).
$$
[Z, Sections 372.3-372.4 and 381-384; R, theorem 2.2.]

**Proof.** The recurrence makes $G_j$ strictly increasing and unbounded, with each increment at least one. First, $V_d$ is a bijection from $X_d$ onto the integer interval $\{0,\ldots,G_d-1\}$. For $d=0$ and $d=1$ this follows from the empty word and the two one-digit words. For $d\ge2$, a legal word whose last digit is zero has exactly the values $0,\ldots,G_{d-1}-1$. A word whose last digit is one has its preceding digit forced to zero, so its values are exactly $G_{d-1},\ldots,G_{d-1}+G_{d-2}-1$. The two ranges are disjoint and exhaust $0,\ldots,G_d-1$, and induction gives uniqueness. In particular, padding any legal prefix with zeros gives $Z(V_d(p))$. Such padded prefixes approximate every point of $K$. The countable product topology is metrizable, and a coordinatewise diagonal subsequence of any sequence in $K$ converges to a binary sequence still satisfying the adjacent-digit restriction. This proves compactness.

There is an elementary preliminary bound independent of the asserted exact formula:
$$
q_{D+1}(x)=q_{D+1}(y)\quad\Longrightarrow\quad q_D(Tx)=q_D(Ty)\qquad(D\ge0).
$$
Indeed, if an actual $00$ starts at some $j<D$, its first position and all retained output digits below $D$ are determined by those $D+1$ input digits. Otherwise the first $00$ starts at or above $D$, or does not exist, and all output digits below $D$ are zero. Iteration gives
$$
q_{L+k}(x)=q_{L+k}(y)\quad\Longrightarrow\quad q_L(T^kx)=q_L(T^ky).
$$
Thus $T$ and all its fixed iterates are continuous. If its first $00$ starts at $j$, the preceding alternating word has value $G_j-1$: its values $A_j$ satisfy $A_0=0$, $A_1=1$, and $A_j=G_{j-1}+A_{j-2}$ for $j\ge2$. Clearing that word and setting position $j$ to one increases a finite input's value by exactly one. The resulting word remains legal, since its lower digits are zero and the retained digit at $j+1$ is zero. Uniqueness of the legal finite expansion therefore gives
$$
T^kZ(n)=Z(n+k).
$$
Moreover, the recurrence and its initial values give
$$
\eta_j:=\phi G_j-G_{j+1}=(-1)^{j+1}\alpha^{j+2}.
$$
The series defining $F$ has uniformly vanishing tails, so $F$ and $H$ are continuous; the displayed identity gives $H(Z(n))=[n\phi]$. Equality on the dense padded core, followed by continuity, yields
$$
H(T^kx)=H(x)+[k\phi]\qquad(x\in K).
$$
This also supplies the successor and phase identities used below without assuming the desired modulus. [Z, Sections 371.2 and 375.2-375.3.]

We next establish the full cylinder geometry, including endpoint ownership. Put
$$
a_0=-\alpha,\qquad b_0=\alpha^2,\qquad I=[a_0,b_0],\qquad c=-\alpha^3.
$$
The total negative and positive coefficient sums bound $F$ below by $a_0$ and above by $b_0$. Equality forces respectively every even digit to be one and every odd digit to be zero, or the reverse. Hence the extreme fibres are $\{u\}$ and $\{v\}$. Every legal infinite word has a unique parsing into blocks $0$ and $10$. Their affine maps are
$$
f_0(t)=\lambda t,\qquad f_{10}(t)=-\alpha^2+\lambda^2t,
$$
with
$$
f_0(I)=[c,b_0],\qquad f_{10}(I)=[a_0,c],\qquad f_0(b_0)=f_{10}(b_0)=c.
$$
These identities follow from $\alpha+\alpha^2=1$. Repeatedly choosing an inverse branch whose image contains a prescribed point of $I$ constructs legal blocks; the residual interval length tends to zero because both branches contract. Their infinite concatenation has precisely the prescribed value. Thus $F[K]=I$.

For a finite block word $w$ of digit length $t$, put
$$
S_w=\sum_{j<t}\eta_jw_j,\qquad s_w=\sum_{j<t}G_jw_j,\qquad f_w(z)=S_w+\lambda^tz.
$$
Splitting the convergent series gives $F(wy)=f_w(F(y))$, and $f_w$ is injective. If two different words have the same real value, at their first distinct block they enter the two branches above, whose images intersect only at $c$. Their remaining tails must both have value $b_0$ and hence must equal $v$. The two words are therefore exactly $w0v$ and $w10v$. Conversely these two words have the same value $f_w(c)$. There cannot be a third preimage, since at the first branching each occupied branch has its endpoint tail uniquely determined. The block word $w$ is recovered as the longest common block prefix of the pair. This proves the real-fibre classification needed here. [Z, Section 372.2.]

Since $b_0-a_0=1$, passing to the circle identifies only the two extreme real values, in addition to the real double fibres. Their common phase is $e_1$, with the orientation
$$
x_1^-=v,\qquad x_1^+=u.
$$
For an internal pair, the identity $\eta_{t+1}=-\lambda^tc$ gives
$$
[f_w(c)]=[\phi(s_w-G_{t+1})].
$$
The empty block word has $t=0$ and gives index $s=2$. For $t\ge1$, a block word of digit length $t$ is exactly a legal word ending in zero. Removing that last zero and applying the proved finite-value bijection shows that $s_w$ runs bijectively through $0,\ldots,G_{t-1}-1$. Consequently the associated indices $s=G_{t+1}-s_w$ run bijectively through
$$
G_t+1,\ldots,G_{t+1}.
$$
These ranges together with $s=2$ exhaust all $s\ge2$. Irrationality of $\phi$ makes the phases distinct. Every other circle fibre is a singleton. A natural phase $[n\phi]$ cannot equal $e_s$, since that would make the nonzero multiple $(n+s)\phi$ an integer. In particular
$$
H^{-1}(\{[n\phi]\})=\{Z(n)\}\qquad(n\ge0).
$$
For $s\ge2$, let $w$ be its unique block word and $t$ its digit length. The correctly oriented pair is
$$
(x_s^-,x_s^+)=\begin{cases}
(w10v,w0v),&t\text{ even},\\
(w0v,w10v),&t\text{ odd}.
\end{cases}
$$
Indeed, before the common prefix is attached, the $10$ branch approaches $c$ from below and the $0$ branch from above. The factor $\lambda^t$ preserves this order for even $t$ and reverses it for odd $t$. At the seam, approach through $b_0$ is the negative side and departure through $a_0$ is the positive side, giving the stated order at $s=1$. For $s\ge2$, the two words first differ exactly at position $t$, where
$$
G_t<s\le G_{t+1}.
$$
[Z, Sections 372.4 and 381.1.]

For $p\in X_D$, $D\ge1$, append its forced next zero if its last digit is one; denote the resulting complete block word by $\widehat p$. Its digit length is $d=D+p_{D-1}$. Hence
$$
F[C_p]=I_p=S_p+\lambda^dI=[\ell_p,b_p].
$$
For $D=0$ the image is $I$. Distinct length-$D$ prefixes give incomparable complete block words. At their first branching the two ancestor interval images meet in only one point, so their descendant images have disjoint interiors. The finitely many positive-length intervals $I_p$ cover $I$. Each has length $\alpha^d<1$, and its endpoints have unique preimages within $C_p$, by the extreme-fibre uniqueness for the remaining tail. An interior point of $I_p$ cannot belong to a second interval, even as that interval's endpoint, since that interval has positive length. Thus the entire fibre above every interior point belongs to $C_p$.

An internal phase is a boundary of this partition exactly when its two lifts have different $D$-prefixes. For $s\ge2$, their first-difference description shows that this happens exactly when $t<D$, equivalently $s\le G_D$. The seam pair already differs at position zero. It follows that the exact circle boundary set is
$$
B_D=\{e_s:1\le s\le G_D\}\qquad(D\ge1).
$$
At depth zero there are no boundaries: $B_0=\varnothing$. If $[\ell_p]=e_i$, $[b_p]=e_j$, and $A_p$ is the oriented open arc given by the image of $(\ell_p,b_p)$, endpoint ownership is exactly
$$
C_p=H^{-1}(A_p)\ \cup\ \{x_i^+,x_j^-\}.
$$
An internal split phase lying in $A_p$ contributes both of its lifts; the left endpoint contributes only its positive lift, and the right endpoint only its negative lift. This formula also treats the seam and does not introduce any artificial boundary at a chosen representative of zero on the circle. [Z, Sections 372.3 and 381.2.]

We must justify how the two lifts, rather than only their phases, move. For fixed $s$, choose $D\ge1$ with $s\le G_D$. A sufficiently small strict negative-side arc at $e_s$ lies in the interior arc of its negative-side $D$-cylinder. Every lift of every point in that small arc therefore belongs to that cylinder. For a sequence of such phases tending to $e_s$, compactness ensures subsequential limits of arbitrary chosen lifts. Continuity of $H$ and closedness of the cylinder force every such limit to be its unique endpoint lift $x_s^-$. Hence the entire lift sequence converges to $x_s^-$. The positive side gives $x_s^+$ in the same way, including at the seam. This argument allows the approaching phases themselves to be other split phases and permits either lift at every term.

Apply this fact to phases approaching $e_{s+k}$ from either side. Their images under the rotation by $[k\phi]$ approach $e_s$ from the same side. Continuity of $T^k$ and the phase identity now give
$$
T^kx_{s+k}^-=x_s^-,\qquad T^kx_{s+k}^+=x_s^+\qquad(s\ge1).
$$
For an earlier pair, the natural phase fibre is instead a singleton, so
$$
T^kx_s^-=T^kx_s^+=Z(k-s)\qquad(1\le s\le k).
$$
Thus no selection of an unverified phase lift has entered these identities. [Z, Section 382.1.]

For an output cylinder $C_p$, $p\in X_L$, with arc and endpoints as above, the complete preimage formula is therefore
$$
(T^k)^{-1}(C_p)=H^{-1}(A_p-[k\phi])\ \cup\ \{x_{i+k}^+,x_{j+k}^-\}.
$$
The interior part follows from the full-fibre formula for $C_p$ and the phase identity. At each endpoint the two possible input lifts are exactly the displayed split pair, and their proven images determine which one belongs. Thus the exact translated cut set is
$$
B_{L,k}=\{e_s:k+1\le s\le k+G_L\}.
$$
Each listed cut is genuine, because its two lifts have different output $L$-prefixes. There are no other cuts by the full preimage formula. In particular the pairs with indices at most $k$, which have already collapsed, introduce no extra boundary. [Z, Section 382.2.]

Suppose now that $G_m\ge G_L+k$. Then necessarily $m\ge L\ge1$, and $B_{L,k}\subseteq B_m$. The interior arc of any input $m$-cylinder contains no translated cut, so, by connectedness of that arc, it is contained in one component of the circle minus $B_{L,k}$. The full-fibre preimage formula puts all lifts over that component in one output preimage cylinder. Check the input cylinder's left endpoint separately: if it is a translated cut, the input cylinder contains its positive lift, exactly the lift assigned to the component immediately on its positive side. If it is not a translated cut, its entire fibre belongs to that same component's preimage. At the right endpoint the identical argument uses the negative lift and the component on its negative side. Both arguments apply at the seam. Thus the entire input cylinder, including both endpoint assignments and all its internal split fibres, lies in a single output preimage cylinder.

It follows that $q_LT^k$ is constant on every actual $q_m$-fibre. Define $f_{k,L,m}(p)$ to be this constant. The map $q_m:K\to X_m$ is onto, so the factor is unique. Choosing the padded representative $Z(V_m(p))$ in the fibre gives the asserted formula for $f$. Conversely, any such factor forces fibre constancy simply by evaluating two representatives of the same prefix. This proves the factorization claim, not merely a comparison of the numbers of prefixes. [Z, Section 383.1; R, theorem 2.2.]

For necessity, put $M=G_L+k\ge2$, and let $t\ge0$ be determined by
$$
G_t<M\le G_{t+1}.
$$
The pair $x_M^-,x_M^+$ first differs at $t$. If $G_m<M$, then $m\le t$, including $m=0$, so the pair has identical $m$-prefixes. Its images are $x_{G_L}^-,x_{G_L}^+$. For index $G_L$, the common block word is $0^{L-1}$, including the empty word when $L=1$. Its two lifts therefore have respective $L$-prefixes, in some order,
$$
0^L\quad\text{and}\quad 0^{L-1}1.
$$
They agree through position $L-2$ and differ at $L-1$. This rules out the fibre implication at every depth with $G_m<M$. Together with sufficiency it proves $J=\mu_k(L)=t+1$ and the exact formula, including all depths below $L$.

Here are finite integer witnesses with a fixed truncation length. Put $N=L+k$. Since every increment of the integer sequence $G_j$ is at least one,
$$
G_N\ge G_L+k=M,
$$
so $t<N$. For $t=0$, let $w$ be empty and $s=0$. For $t\ge1$, set $s=G_{t+1}-M$, so $0\le s<G_{t-1}$; take the unique length-$(t-1)$ legal word of value $s$ and append zero to obtain $w$. In both cases the two lifts, without imposing their sign order, are
$$
\xi=w0v,\qquad \xi'=w10v.
$$
Their zero-padded $N$-digit truncations are $Z(a)$ and $Z(b)$, where explicitly
$$
a=s+\sum_{\substack{h\ge0\\t+2+2h<N}}G_{t+2+2h},\qquad
b=s+G_t+\sum_{\substack{h\ge0\\t+3+2h<N}}G_{t+3+2h}.
$$
All sums are finite and an empty sum is zero. Both truncated words are legal, and the finite-value bijection gives $0\le a,b<G_N$. Their first difference is still at $t$, so they are distinct. The preliminary $N=L+k$ precision bound gives
$$
q_LT^kZ(a)=q_LT^k\xi,\qquad q_LT^kZ(b)=q_LT^k\xi'.
$$
The two output prefixes are therefore exactly $0^L$ and $0^{L-1}1$, in some order. Since $T^kZ(n)=Z(n+k)$, these are the claimed actual integer witnesses. In topological terms, the witnesses lie in the nonempty clopen tests specifying the required common input prefix and the two different output prefixes; the construction realizes them by explicit points of the dense padded core. It follows in particular that restriction to that core cannot improve the minimum. [Z, Section 384.1.]

Finally, $L=0$ gives the constant empty observation, so its minimum is zero for every $k$. For $L\ge1$, the strictly increasing sequence $G_m$ makes its first successful index characterize precisely $G_{m-1}<G_L+k\le G_m$ for $m\ge1$. Since $G_0=1<G_L+k$, depth zero never succeeds at positive output depth. For $k=0$ the first successful index is $L$. For $k=1$, index $L$ fails and index $L+1$ succeeds. The already proved inequality $G_{L+k}\ge G_L+k$ gives the upper bound. No strictness is introduced at a successful Fibonacci threshold. This completes the proof.

**Definition 24.3 (Prefix ultrametric and optimal distortion).** For $x,y\in K$, define
$$
d_*(x,y)=\begin{cases}
0,&x=y,\\
2^{-\min\{j\ge0:x_j\ne y_j\}},&x\ne y.
\end{cases}
$$
Set
$$
C(k)=\operatorname{Lip}_{d_*}(T^k)=\sup_{x\ne y}\frac{d_*(T^kx,T^ky)}{d_*(x,y)}.
$$
This is the prefix metric on the digit carrier, not the sum metric $d_\Sigma(x,y)=\sum_{j\ge0}2^{-j-1}|x_j-y_j|$ of [Z, Definition 371.1]. In particular $d_*(Z(0),Z(1))=1$, while $d_\Sigma(Z(0),Z(1))=1/2$.

**theorem 24.4 (Optimal Fibonacci-step distortion and failure of a uniform-in-time budget).** Define
$$
r(k)=\min\{r\ge0:G_{r+1}\ge k+2\},\qquad \beta=\log_\phi2.
$$
For every $k\ge0$,
$$
\sup_{L\ge1}\bigl(\mu_k(L)-L\bigr)=\mu_k(1)-1=r(k),
$$
$$
\boxed{\ C(k)=2^{r(k)}.\ }
$$
The supremum defining $C(k)$ is attained, and it is attained by a pair of actual finite integer expansions. More precisely, at every $L\ge1$ the witnesses of theorem 24.2 attain the ratio $2^{\mu_k(L)-L}$; taking $L=1$ attains the optimal constant.

For every integer $r\ge0$, the exact plateaus are
$$
C(k)=2^r\quad\Longleftrightarrow\quad G_r-1\le k\le G_{r+1}-2.
$$
In particular $C(0)=1$, and for all $k\ge0$,
$$
\frac14(k+1)^\beta\le C(k)\le(k+1)^\beta.
$$
For all $k,h\ge0$,
$$
C(k+h)\le C(k)C(h),\qquad r(k+h)\le r(k)+r(h).
$$
Equality is not required; for example $C(4)=8<16=C(2)^2$.

Each fixed $T^k$ is uniformly continuous on the compact metric space $(K,d_*)$. There is nevertheless no finite input depth that determines the first output digit uniformly over all $k$. Indeed,
$$
\mu_{G_m-1}(1)=m+1\qquad(m\ge0).
$$
The family $\{T^k:k\ge0\}$ is not equicontinuous, even at $Z(0)$, and this failure has witnesses from the finite integer core. With the parameter space $\mathbb N_0$ given its discrete topology, the evaluation map
$$
\mathbb N_0\times K\longrightarrow K,\qquad (k,x)\longmapsto T^kx
$$
is nonetheless jointly continuous.

**Proof.** Agreement of two pairs of sequences through the shorter common prefix gives
$$
d_*(x,z)\le\max\{d_*(x,y),d_*(y,z)\},
$$
so $d_*$ is an ultrametric. Its exact relation to the observations is
$$
q_D(x)=q_D(y)\quad\Longleftrightarrow\quad d_*(x,y)\le2^{-D}\qquad(D\ge0).
$$
Thus its topology is the product topology. Also, the first differing term and the full geometric tail give $d_*/2\le d_\Sigma\le d_*$. This identifies the compact topology without identifying the two metrics or transferring their optimal Lipschitz constants.

Fix $r\ge0$ and set $D_r(L)=G_{L+r}-G_L$ for $L\ge1$. Using the recurrence at indices at least one,
$$
D_r(L+1)-D_r(L)=G_{L+r-1}-G_{L-1}\ge0.
$$
Consequently
$$
G_{L+r}-G_L\ge G_{r+1}-G_1=G_{r+1}-2.
$$
For $r=r(k)$ the right side is at least $k$. The exact modulus theorem therefore gives $\mu_k(L)\le L+r(k)$ for every $L\ge1$. At $L=1$, the first successful index $m$ satisfies $G_m\ge k+2$ and is at least one, so it is exactly $r(k)+1$. This proves both the upper bound for the supremum and its attainment at $L=1$, including $k=0$.

To obtain the precise metric constant, suppose $x,y$ first differ at $j$ and their images under $T^k$ are distinct and first differ at $\ell$. The images disagree under $q_{\ell+1}$. If $j\ge\mu_k(\ell+1)$, the inputs would agree at that sufficient precision, a contradiction. Hence
$$
j\le\mu_k(\ell+1)-1,
$$
and therefore
$$
\frac{d_*(T^kx,T^ky)}{d_*(x,y)}
=2^{j-\ell}
\le2^{\mu_k(\ell+1)-(\ell+1)}
\le2^{r(k)}.
$$
If the images coincide, the ratio is zero and the same upper bound holds. Conversely, the split pair with index $M=G_L+k$ first differs at $\mu_k(L)-1$ and its images first differ at $L-1$, so its ratio is exactly $2^{\mu_k(L)-L}$. The finite witnesses in theorem 24.2 preserve these very same first-difference positions. Taking $L=1$ proves actual attainment of $2^{r(k)}$ on the finite core. This supplies the lower bound and settles both off-by-one indices.

The threshold definition gives $G_r<k+2\le G_{r+1}$ at the successful value of $r$, also for $r=0$, where necessarily $k=0$. Since these thresholds are integers, this is precisely $G_r-1\le k\le G_{r+1}-2$, proving the plateau formula. For the quantitative growth estimate, induction from $G_0=1$, $G_1=2$, and $\phi^2=\phi+1$ gives
$$
\phi^n\le G_n\le\phi^{n+1}\qquad(n\ge0).
$$
Putting $r=r(k)$ in the threshold inequalities yields
$$
\phi^r\le G_r\le k+1<G_{r+1}\le\phi^{r+2}.
$$
Raising to the positive power $\beta$, with $\phi^\beta=2$, gives
$$
2^r\le(k+1)^\beta<4\,2^r,
$$
which implies the stated two-sided bounds. The exact law remains the Fibonacci-step formula, not an equality with a smooth power function.

For composition, the already proved Lipschitz inequalities give, for every $x,y$,
$$
d_*(T^{k+h}x,T^{k+h}y)
\le C(k)d_*(T^hx,T^hy)
\le C(k)C(h)d_*(x,y).
$$
Taking the supremum proves submultiplicativity. Substituting $C(n)=2^{r(n)}$ and using strict monotonicity of $2^s$ proves the integer subadditivity. The values $G_2=3$, $G_3=5$, $G_4=8$ give $r(2)=2$ and $r(4)=3$, proving the strict example.

The uniform-in-time precision obstruction follows directly from actual fibres, rather than from growth of metric constants. For any $m\ge0$, the nonnegative integer $k=G_m-1$ satisfies
$$
G_m<k+2=G_m+1\le G_{m+1}.
$$
Thus theorem 24.2 gives $\mu_k(1)=m+1$ and supplies finite inputs with the same $m$-prefix but different first output digits. This rules out any common finite depth at the first output digit.

For the stronger pointwise failure at $Z(0)$, take $j\ge0$ and
$$
k_j=G_{j+1}-2,\qquad M_j=k_j+2=G_{j+1}.
$$
The split pair at $M_j$ has common block word $0^j$ and consists, without specifying its sign order, of
$$
0^{j+1}v\quad\text{and}\quad 0^j10v.
$$
Its two images under $T^{k_j}$ have opposite first digits. Apply the finite truncation construction of theorem 24.2 with $L=1$ and $N=k_j+1$. It gives two finite-core points both starting with $j$ zeros whose images still have opposite first digits. At least one of these points, call it $y_j$, has an output first digit different from that of $T^{k_j}Z(0)$. Therefore
$$
d_*(y_j,Z(0))\le2^{-j}\longrightarrow0,\qquad
d_*(T^{k_j}y_j,T^{k_j}Z(0))=1.
$$
The single output tolerance $1/2$ consequently has no neighborhood of $Z(0)$ working for every iterate. This proves non-equicontinuity with actual finite integer inputs.

Finally, each fixed iterate is continuous by theorem 24.2 and has the explicit finite modulus proved there; compactness also implies its uniform continuity. For the joint evaluation map with discrete parameter, at any $(k,x)$ one may restrict to the open slice $\{k\}\times K$, where continuity is just continuity of $T^k$. Thus joint continuity with discrete time coexists with failure of a state-precision modulus uniform over all times. The negative conclusion concerns the latter quantifier order, not a failure of fixed-map continuity.

## 追加锚（本行以下为增补区）
## 25. 精确 Zeckendorf 闭图上归一化实有符号结合核的完全分类

**定义 25.0（载体、相位和固定定向）。** 取 $\mathbb N=\{0,1,2,\ldots\}$、$\mathbb N_{>0}=\{1,2,\ldots\}$，置
$$
G_0=1,\qquad G_1=2,\qquad G_{j+2}=G_{j+1}+G_j,\qquad
\phi=\frac{1+\sqrt5}{2},\qquad \alpha=\phi^{-1},
$$
$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ 对所有 }j\},\qquad
F(x)=\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j,\qquad
H(x)=[F(x)]\in\mathbb T=\mathbb R/\mathbb Z.
$$
记 $Z(n)$ 为以权 $G_j$ 展开的有限 Zeckendorf 规范字补零所得的点，$0_K=Z(0)$，并沿用定义16.0的闭图
$$
\Gamma=\overline{\{(Z(a),Z(b),Z(a+b)):a,b\in\mathbb N\}}^{\,K^3},\qquad
\Gamma(x,y)=\{w:(x,y,w)\in\Gamma\}.
$$
对 $m\ge1$，记
$$
E_m=[-m\phi],\qquad E=\{E_m:m\ge1\},\qquad
x_m^+=z_{E_m}^{+1},\qquad x_m^-=z_{E_m}^{-1}.
$$
这里的标记严格取定义16.3的相位正、负侧定向，不另行逐纤维交换；特别 $x_1^+=(10)^{\mathbb N}$、$x_1^-=(01)^{\mathbb N}$。[^rro25-graph]

**假设 25.1（精确纤维与精确闭图）。** 本节采用下述显式前提。$H$ 满射，并且
$$
H^{-1}(\{E_m\})=\{x_m^+,x_m^-\},\qquad x_m^+\ne x_m^-,
$$
$$
H^{-1}(\{\theta\})=\{k_\theta\}\quad(\theta\notin E),\qquad
H^{-1}(\{[n\phi]\})=\{Z(n)\}\quad(n\in\mathbb N).
$$
特别 $k_0=0_K$。[^rro25-phase] 定义
$$
\mathcal S(x)=
\begin{cases}
\{+1\},&x=x_m^+\text{，某个 }m\ge1,\\
\{-1\},&x=x_m^-\text{，某个 }m\ge1,\\
\{-1,+1\},&H(x)\notin E.
\end{cases}
$$
对 $\sigma=H(x)+H(y)$，要求准确等式
$$
\Gamma(x,y)=
\begin{cases}
\{k_\sigma\},&\sigma\notin E,\\
\{x_r^s:s\in\mathcal S(x)\cup\mathcal S(y)\},&\sigma=E_r.
\end{cases}
$$
其中 $x_r^{+1}=x_r^+$、$x_r^{-1}=x_r^-$。这是定理16.4的完整输入纤维公式，而不是仅有 $H(w)=H(x)+H(y)$ 的相位条件。[^rro25-graph]

**定义 25.2（归一化实有符号核与有限卷积）。** 令
$$
A=\mathbb R^{(K)}
=\{a:K\to\mathbb R:\operatorname{supp}(a)\text{ 有限}\},\qquad
\operatorname{supp}(a)=\{x:a(x)\ne0\},
$$
$$
\delta_x(w)=
\begin{cases}1,&w=x,\\0,&w\ne x,\end{cases}
\qquad
\varepsilon(a)=\sum_{x\in K}a(x),\qquad
A_\theta=\{a\in A:\operatorname{supp}(a)\subseteq H^{-1}(\{\theta\})\}.
$$
所有和均为有限和。$\varepsilon(a)=1$ 表示仿射系数归一化，不要求各系数非负。[^rro25-affine] 一个满足精确闭图支撑条件的归一化实有符号核，是映射 $P:K^2\to A$，满足
$$
\varepsilon(P_{x,y})=1,\qquad
\operatorname{supp}(P_{x,y})\subseteq\Gamma(x,y).
$$
这里要求的是支撑包含于准确的 $\Gamma(x,y)$，不要求支撑等于该集合。定义双线性乘法
$$
a*b=\sum_{x,y\in K}a(x)b(y)P_{x,y},
\qquad \delta_x*\delta_y=P_{x,y}.
$$
称 $P$ 结合，若对每个有序三元组 $(x,y,z)\in K^3$，
$$
(\delta_x*\delta_y)*\delta_z
=\delta_x*(\delta_y*\delta_z).
$$
交换律和单位律不属于此定义。用 $0_A$ 区别于点 $0_K$。另记 $\mathbb R[\mathbb T]$ 为基向量 $b_\theta$ 的有限实形式和，乘法由
$$
b_\theta b_\rho=b_{\theta+\rho}
$$
双线性扩张，并定义线性映射 $H_\#:A\to\mathbb R[\mathbb T]$，使
$$
H_\#(\delta_x)=b_{H(x)}.
$$
此处的群代数只使用有限形式和。[^rro25-algebra]

**定理 25.3（有限延拓、增广与相位分次）。** 定义25.2的乘法良定义，且
$$
\varepsilon(a*b)=\varepsilon(a)\varepsilon(b),\qquad
A_\theta*A_\rho\subseteq A_{\theta+\rho},\qquad
H_\#(a*b)=H_\#(a)H_\#(b).
$$
$H_\#$ 满射。点质量有序三元组上的结合律等价于整个 $A$ 上的结合律。

**证明。** 对给定 $a,b$，仅有有限多个输入对参与求和，每个 $P_{x,y}$ 又有有限支撑。因此乘积的支撑包含于有限多个有限集的并。由各核的系数和为一，
$$
\varepsilon(a*b)
=\sum_{x,y}a(x)b(y)\varepsilon(P_{x,y})
=\sum_{x,y}a(x)b(y)
=\varepsilon(a)\varepsilon(b).
$$
假设25.1使 $P_{x,y}$ 支撑于相位 $H(x)+H(y)$；这给分次包含，并给
$$
H_\#(P_{x,y})=b_{H(x)+H(y)}.
$$
双线性扩张即得乘法相容性。每个相位有原像，所以每个 $b_\theta$ 都在像中，满射成立。最后，任意 $a,b,c$ 的结合子等于有限和
$$
(a*b)*c-a*(b*c)
=\sum_{x,y,z}a(x)b(y)c(z)
\bigl((\delta_x*\delta_y)*\delta_z-\delta_x*(\delta_y*\delta_z)\bigr).
$$
因此点质量上的结合律推出全空间结合律，反向是限制。证毕。

**定理 25.4（零切片唯一化与有符号平均恒等式）。** 设 $P$ 结合，置 $e=\delta_{0_K}$。存在唯一一族 $\pi_\theta\in A_\theta$，使
$$
\varepsilon(\pi_\theta)=1,\qquad
e*\delta_x=\delta_x*e=\pi_{H(x)}.
$$
此外 $\pi_0=e$、$e*e=e$，并且对 $a\in A_\theta$，
$$
e*a=a*e=\varepsilon(a)\pi_\theta.
$$
对任意 $x,y\in K$ 及 $\theta,\rho\in\mathbb T$，
$$
\pi_{H(x)}*\delta_y=\delta_x*\pi_{H(y)}
=\pi_{H(x)+H(y)},\qquad
\pi_\theta*\pi_\rho=\pi_{\theta+\rho}.
$$

**证明。** $\phi$ 无理，故 $E_m$ 两两不同，且 $E_m+E_n=E_{m+n}$。置 $\tau=[1/2]$。$\tau\notin E$：否则 $m\phi$ 与一个半整数相等，矛盾。同样，
$$
(E+\tau)\cap E=\varnothing,
$$
因为 $E_m+\tau=E_n$ 会使 $(n-m)\phi+1/2$ 为整数；$n=m$ 时不可能，$n\ne m$ 时则迫使 $\phi$ 有理。

令 $h=k_\tau$、$a_h=\delta_h$。相位零只有 $0_K$，故归一化与精确支撑给
$$
a_h*a_h=e.
$$
固定 $\theta=E_m$。对该纤维的任意 $x$，因 $\theta+\tau\notin E$，
$$
a_h*\delta_x=\delta_x*a_h=\delta_{k_{\theta+\tau}}.
$$
所以
$$
e*\delta_x=a_h*(a_h*\delta_x)
=a_h*\delta_{k_{\theta+\tau}},
$$
$$
\delta_x*e=(\delta_x*a_h)*a_h
=\delta_{k_{\theta+\tau}}*a_h.
$$
左、右零切片各自在该相位纤维上恒定。非分裂纤维只有一个输入点，恒定性也成立。分别将这两个切片记为 $L_\theta,R_\theta$。它们均属于 $A_\theta$，且系数和均为一。

对 $H(x)=\theta$，结合律在 $(0_K,x,0_K)$ 上给
$$
L_\theta*e=e*R_\theta.
$$
逐项使用右切片恒定性，左边是 $\varepsilon(L_\theta)R_\theta=R_\theta$；逐项使用左切片恒定性，右边是 $\varepsilon(R_\theta)L_\theta=L_\theta$。因此二者相等，记为 $\pi_\theta$。此步只使用系数和为一，允许负系数。满射性保证每个 $\pi_\theta$ 都由这些切片唯一确定。对 $a\in A_\theta$ 逐项求和，即得所述平均恒等式。零相位单点性还给 $\pi_0=e$、$e*e=e$。

最后，若 $H(x)=\theta,H(y)=\rho$，则
$$
\pi_\theta*\delta_y
=(e*\delta_x)*\delta_y
=e*P_{x,y}
=\pi_{\theta+\rho},
$$
$$
\delta_x*\pi_\rho
=\delta_x*(\delta_y*e)
=P_{x,y}*e
=\pi_{\theta+\rho}.
$$
在第二槽对系数和为一的 $\pi_\rho$ 求和，得到 $\pi_\theta*\pi_\rho=\pi_{\theta+\rho}$。整个论证没有交换任意两个未知乘积。证毕。

**定理 25.5（所有实切片系数下的实际基）。** 任取实数序列 $(p_m)_{m\ge1}$，定义
$$
\pi_{E_m}=p_m\delta_{x_m^+}+(1-p_m)\delta_{x_m^-},\qquad
\pi_\theta=\delta_{k_\theta}\quad(\theta\notin E),\qquad
v_m=\delta_{x_m^+}-\delta_{x_m^-}.
$$
不论该序列是否来自结合核，集合
$$
\{\pi_\theta:\theta\in\mathbb T\}\ \cup\ \{v_m:m\ge1\}
$$
都是 $A$ 的代数基。准确地，
$$
\delta_{x_m^+}=\pi_{E_m}+(1-p_m)v_m,\qquad
\delta_{x_m^-}=\pi_{E_m}-p_m v_m.
$$
若
$$
V=\operatorname{span}_{\mathbb R}\{\pi_\theta:\theta\in\mathbb T\},\qquad
J=\operatorname{span}_{\mathbb R}\{v_m:m\ge1\},
$$
则 $A=V\oplus J$、$\ker H_\#=J$，且 $H_\#|_V$ 是到 $\mathbb R[\mathbb T]$ 的线性同构。

**证明。** 两个显示的逆变换逐项展开即可验证；非分裂纤维的点质量就是 $\pi_\theta$。因此每个点质量，进而每个有限支撑形式和，都有这些向量的有限线性展开。

为证线性无关，取任意有限线性关系
$$
\sum_\theta a_\theta\pi_\theta+\sum_m b_m v_m=0_A.
$$
按相位分组。每个相位分量的系数总和为 $a_\theta$，因为 $\varepsilon(\pi_\theta)=1$、$\varepsilon(v_m)=0$。故所有 $a_\theta=0$。余下的 $v_m$ 分属不同相位，而且各自有两个不同支撑点，其系数分别为一与负一，故所有 $b_m=0$。这证明基与直和，尤其包括 $p_m=0$ 或 $p_m=1$ 的情形，没有除以这些数。

又 $H_\#(\pi_\theta)=b_\theta$、$H_\#(v_m)=0$。利用已证的唯一有限展开，核恰为 $J$，在 $V$ 上的限制把一组基双射到另一组基，故为所述同构。证毕。

**定理 25.6（全部乘法自由度及同号强制方程）。** 对任意结合核，以定理25.4的切片唯一写成
$$
\pi_{E_m}=p_m\delta_{x_m^+}+(1-p_m)\delta_{x_m^-}.
$$
存在唯一实数 $c_{m,n}$，使其全部乘法在定理25.5的基上满足
$$
\pi_\theta*\pi_\rho=\pi_{\theta+\rho},\qquad
\pi_\theta*v_m=v_m*\pi_\theta=0_A,\qquad
v_m*v_n=c_{m,n}v_{m+n}.
$$
对所有正整数 $m,n,\ell$，有
$$
(1-p_m)(1-p_n)c_{m,n}=1-p_{m+n},\qquad
p_mp_nc_{m,n}=-p_{m+n},
$$
$$
(1-p_m-p_n)c_{m,n}=1,\qquad
c_{m,n}=\frac1{1-p_m-p_n}\ne0,
$$
$$
p_{m+n}=\frac{p_mp_n}{p_m+p_n-1},\qquad
c_{m,n}c_{m+n,\ell}=c_{n,\ell}c_{m,n+\ell}.
$$
特别 $p_m+p_n\ne1$、$p_m\ne1/2$，而且乘法必定交换。

**证明。** 非分裂切片由单点性唯一确定；分裂切片由总和一唯一确定 $p_m$。定理25.4使 $\pi_\theta$ 与同一相位的两个点质量相乘时得到相同结果，两者相减给两侧湮灭恒等式。

由相位分次，$v_m*v_n$ 属于 $A_{E_{m+n}}$；其系数和为 $\varepsilon(v_m)\varepsilon(v_n)=0$。该二点纤维上系数和为零的空间恰为 $\mathbb Rv_{m+n}$，所以 $c_{m,n}$ 存在且唯一。

精确闭图在两个同号分裂输入处给单点支撑，因此归一化迫使
$$
\delta_{x_m^+}*\delta_{x_n^+}=\delta_{x_{m+n}^+},\qquad
\delta_{x_m^-}*\delta_{x_n^-}=\delta_{x_{m+n}^-}.
$$
将定理25.5的逆变换代入，分别得到
$$
\pi_{E_{m+n}}+(1-p_m)(1-p_n)c_{m,n}v_{m+n}
=\pi_{E_{m+n}}+(1-p_{m+n})v_{m+n},
$$
$$
\pi_{E_{m+n}}+p_mp_nc_{m,n}v_{m+n}
=\pi_{E_{m+n}}-p_{m+n}v_{m+n}.
$$
比较非零向量 $v_{m+n}$ 的系数即得前两个方程。第一个方程减去第二个方程，得到
$$
\bigl((1-p_m)(1-p_n)-p_mp_n\bigr)c_{m,n}=1,
$$
即 $(1-p_m-p_n)c_{m,n}=1$。因此分母和 $c_{m,n}$ 都不为零，所列递推随之成立；取 $n=m$ 排除每个 $p_m=1/2$。

定理25.3允许将结合律用于 $v_m,v_n,v_\ell$。比较非零向量 $v_{m+n+\ell}$ 的系数，得到余循环等式。最后，$c_{m,n}$ 的已证公式关于 $m,n$ 对称；相位基上的乘法交换，交叉乘积两侧都为零。因此所有基向量两两交换，双线性扩张给整个 $A$ 的交换律。证毕。

**定理 25.7（包括退化项的参数穷尽）。** 定理25.6的系数必且仅可能落入下列参数形式之一：
$$
p_m=\frac{t^m}{t^m-1},\qquad
c_{m,n}=-\frac{(t^m-1)(t^n-1)}{t^{m+n}-1}
\quad\text{，某个 }t\in\mathbb R\setminus\{-1,1\},
$$
或
$$
p_m=1,\qquad c_{m,n}=-1\quad\text{ 对所有 }m,n\ge1.
$$
第一种形式中的 $t=0$ 正是 $p_m=0,c_{m,n}=1$ 的情形。任何一项 $p_m=0$ 都迫使全部项为零；任何一项 $p_m=1$ 都迫使全部项为一。其余情形的每一项都避开零和一。

**证明。** 先作必要性分类。若 $p_1=0$，由 $p_mp_1c_{m,1}=-p_{m+1}$ 得 $p_{m+1}=0$，所以全部项为零，再由 $(1-p_m-p_n)c_{m,n}=1$ 得 $c_{m,n}=1$。若 $p_1=1$，由 $(1-p_m)(1-p_1)c_{m,1}=1-p_{m+1}$ 得全部项为一，并得 $c_{m,n}=-1$。

若 $p_1\notin\{0,1\}$，用
$$
p_{m+1}=-p_mp_1c_{m,1},\qquad
1-p_{m+1}=(1-p_m)(1-p_1)c_{m,1}
$$
归纳。$c_{m,1}\ne0$ 保证每一步的两个右端都非零。因此所有 $p_m$ 都不等于零或一。这也排除了在较大指标才出现退化项的可能性。

现在仅在这一非退化情形定义
$$
t_m=-\frac{p_m}{1-p_m}.
$$
两个强制方程及各个非零分母给
$$
t_{m+n}
=\frac{p_mp_nc_{m,n}}{(1-p_m)(1-p_n)c_{m,n}}
=t_mt_n.
$$
置 $t=t_1$，对 $m$ 归纳得 $t_m=t^m$。每个 $t_m$ 非零，而且 $t_m=1$ 会给 $-p_m=1-p_m$，矛盾。因此 $t^m\ne1$。特别 $t\ne1$，且 $t=-1$ 会使 $t_2=1$，也被排除。解出 $p_m$ 得
$$
p_m=\frac{t^m}{t^m-1}.
$$
代入 $c_{m,n}=1/(1-p_m-p_n)$，得到
$$
1-p_m-p_n
=-\frac{t^{m+n}-1}{(t^m-1)(t^n-1)},
$$
从而得到所列 $c_{m,n}$。

反向核对这些系数方程本身。实数 $t\ne\pm1$ 的任意正整数次幂均不等于一：奇数次幂等于一只能有 $t=1$；偶数次幂等于一只能有 $t=\pm1$。所以全部分母非零。令 $A_m=t^m-1$，则
$$
1-p_m=-\frac1{A_m},\qquad
c_{m,n}=-\frac{A_mA_n}{A_{m+n}}.
$$
直接相乘给
$$
(1-p_m)(1-p_n)c_{m,n}=-\frac1{A_{m+n}}=1-p_{m+n},
$$
$$
p_mp_nc_{m,n}=-\frac{t^{m+n}}{A_{m+n}}=-p_{m+n}.
$$
余循环的两个乘积都等于
$$
\frac{A_mA_nA_\ell}{A_{m+n+\ell}}.
$$
这些计算包括 $t=0$，因为全部指标严格为正，不涉及零次幂。对于另列的常值 $p_m=1,c_{m,n}=-1$，两个强制方程分别为零等于零、负一等于负一，余循环两边均为一。故列出的参数也满足全部系数方程；其确实给出全载体核将在定理25.9证明。证毕。

**定义 25.8（全部候选核的显式构造）。** 取参数集合
$$
\Lambda=(\mathbb R\setminus\{-1,1\})\sqcup\{\infty\}.
$$
$\infty$ 是另加的形式符号，不表示任何极限。对有限参数 $t$，采用定理25.7的 $p_m,c_{m,n}$；对参数 $\infty$，另行定义 $p_m=1,c_{m,n}=-1$。由这些系数和定理25.5组成实际基，并在该基上定义
$$
\pi_\theta*_t\pi_\rho=\pi_{\theta+\rho},\qquad
\pi_\theta*_t v_m=v_m*_t\pi_\theta=0_A,\qquad
v_m*_t v_n=c_{m,n}v_{m+n}.
$$
双线性扩张后，定义
$$
P^{(t)}_{x,y}=\delta_x*_t\delta_y.
$$
每个参数的 $\pi_\theta,p_m,c_{m,n}$ 均取该参数自己的值。

**定理 25.9（全载体构造、全部三元组与精确同号支撑）。** 对每个 $t\in\Lambda$，定义25.8给出一个归一化实有符号结合核。其支撑包含于准确的 $\Gamma(x,y)$，而且
$$
P^{(t)}_{Z(a),Z(b)}=\delta_{Z(a+b)}\qquad(a,b\in\mathbb N).
$$
若至少一个输入非分裂，则
$$
P^{(t)}_{x,y}=\pi_{H(x)+H(y)}.
$$
若两个输入为分裂点，则同号输入准确地给出
$$
P^{(t)}_{x_m^+,x_n^+}=\delta_{x_{m+n}^+},\qquad
P^{(t)}_{x_m^-,x_n^-}=\delta_{x_{m+n}^-}.
$$
对有限参数，其两个有序异号公式为
$$
P^{(t)}_{x_m^+,x_n^-}
=\frac{t^n(t^m-1)}{t^{m+n}-1}\delta_{x_{m+n}^+}
+\frac{t^n-1}{t^{m+n}-1}\delta_{x_{m+n}^-},
$$
$$
P^{(t)}_{x_m^-,x_n^+}
=\frac{t^m(t^n-1)}{t^{m+n}-1}\delta_{x_{m+n}^+}
+\frac{t^m-1}{t^{m+n}-1}\delta_{x_{m+n}^-}.
$$
对形式参数 $\infty$，两个异号输出均为 $\delta_{x_{m+n}^+}$。

**证明。** 定理25.5保证构造所用的确实是一组基，每个乘法规则的输出都是有限形式和，所以双线性乘法良定义。$\varepsilon(\pi_\theta)=1$、$\varepsilon(v_m)=0$。逐对检查基向量可见
$$
\varepsilon(u*_t v)=\varepsilon(u)\varepsilon(v),
$$
故此恒等式由双线性对所有形式和成立，特别每个点质量乘积的系数和为一。

逐类验证结合律。三个相位基向量的两个括号均给 $\pi_{\theta+\rho+\sigma}$。三个差分基向量的两个括号分别为
$$
c_{m,n}c_{m+n,\ell}v_{m+n+\ell},\qquad
c_{n,\ell}c_{m,n+\ell}v_{m+n+\ell},
$$
由定理25.7中已经直接计算的余循环相等；有限参数的共同标量为
$$
\frac{(t^m-1)(t^n-1)(t^\ell-1)}{t^{m+n+\ell}-1},
$$
形式参数 $\infty$ 的共同标量为一。其余六种有序类型逐一为
$$
(\pi_\theta*_t\pi_\rho)*_t v_m
=\pi_\theta*_t(\pi_\rho*_t v_m)=0_A,
$$
$$
(\pi_\theta*_t v_m)*_t\pi_\rho
=\pi_\theta*_t(v_m*_t\pi_\rho)=0_A,
$$
$$
(v_m*_t\pi_\theta)*_t\pi_\rho
=v_m*_t(\pi_\theta*_t\pi_\rho)=0_A,
$$
$$
(\pi_\theta*_t v_m)*_t v_n
=\pi_\theta*_t(v_m*_t v_n)=0_A,
$$
$$
(v_m*_t\pi_\theta)*_t v_n
=v_m*_t(\pi_\theta*_t v_n)=0_A,
$$
$$
(v_m*_t v_n)*_t\pi_\theta
=v_m*_t(v_n*_t\pi_\theta)=0_A.
$$
每个等式均由混合乘积为零及差分乘积仍为差分倍数得到。因此全部基三元组满足结合律；有限三线性扩张覆盖整个 $A$，当然也覆盖全部点质量有序三元组。

还须验证比相位相容更强的实际支撑。若至少一个输入非分裂，其点质量为某个 $\pi_\theta$；另一个输入为 $\pi_\rho$ 或 $\pi_\rho$ 加一个差分倍数，乘积遂为 $\pi_{\theta+\rho}$。和相位非分裂时，这是唯一允许点的点质量；和相位分裂时，非分裂输入的符号集含两个符号，因此 $\Gamma(x,y)$ 允许两个分支，$\pi_{\theta+\rho}$ 的支撑合法。

若两个输入分别位于 $E_m,E_n$，和相位必为 $E_{m+n}$。两个同号乘积展开为
$$
\pi_{E_{m+n}}+(1-p_m)(1-p_n)c_{m,n}v_{m+n}
=\pi_{E_{m+n}}+(1-p_{m+n})v_{m+n}
=\delta_{x_{m+n}^+},
$$
$$
\pi_{E_{m+n}}+p_mp_nc_{m,n}v_{m+n}
=\pi_{E_{m+n}}-p_{m+n}v_{m+n}
=\delta_{x_{m+n}^-}.
$$
这证明同号处的反号系数准确为零，并非只检查整个二点相位纤维。

对于输入 $(x_m^+,x_n^-)$，展开为
$$
\pi_{E_{m+n}}-(1-p_m)p_nc_{m,n}v_{m+n}.
$$
其正支系数利用 $p_{m+n}=-p_mp_nc_{m,n}$ 化为 $-p_nc_{m,n}$；有限参数下这等于
$$
\frac{t^n(t^m-1)}{t^{m+n}-1}.
$$
负支系数是一减正支系数，等于 $(t^n-1)/(t^{m+n}-1)$。另一个有序异号公式同理由展开 $\pi_{E_{m+n}}-p_m(1-p_n)c_{m,n}v_{m+n}$ 得到。二者的两个系数都相加为一，且异号输入允许两个分支，所以即使有负系数，其支撑仍合法。形式参数 $\infty$ 下，$p_m=p_n=1$ 使两个异号展开中的差分修正均为零，$\pi_{E_{m+n}}=\delta_{x_{m+n}^+}$。

这些情况穷尽输入对，完成精确支撑验证。最后，自然数相位及其和相位都非分裂，假设25.1使相应唯一点为 $Z(a),Z(b),Z(a+b)$，从而得到自然数核心等式。证毕。

**定理 25.10（完全分类及单个切片系数参数）。** 在假设25.1下，映射
$$
t\longmapsto P^{(t)}
$$
是 $\Lambda$ 到全部归一化实有符号结合核的双射。等价地，全部核由一个实数
$$
q=P_{0_K,x_1^+}(x_1^+)\in\mathbb R\setminus\{1/2\}
$$
唯一参数化。两种参数的转换为
$$
q=\frac{t}{t-1}\quad(t\ne\infty),\qquad
q=1\quad(t=\infty),
$$
$$
t=\frac{q}{q-1}\quad(q\ne1),\qquad
t=\infty\quad(q=1).
$$
若置 $D_m(q)=q^m-(q-1)^m$，则所有情形统一为
$$
p_m=\frac{q^m}{D_m(q)},\qquad
c_{m,n}=-\frac{D_m(q)D_n(q)}{D_{m+n}(q)}.
$$

**证明。** 对任意给定核，定理25.4从其实际零切片唯一确定全部 $\pi_\theta$，定理25.6唯一确定其余基乘法系数，并证明不存在额外混合项。定理25.7穷尽这些系数：全零情形对应 $t=0$，全一情形对应 $\infty$，非退化情形对应唯一的 $t=-p_1/(1-p_1)$。因此在定理25.5的实际基上，原乘法与定义25.8的对应乘法完全相同；双线性和张成性使它们在全部点质量上相同。这证明满射，不留下额外的非交换或零余循环分支。

反向，对于构造出的核，由 $\delta_{0_K}=\pi_0$ 和混合湮灭式，
$$
P^{(t)}_{0_K,x_m^+}=P^{(t)}_{0_K,x_m^-}=\pi_{E_m}.
$$
所以零切片读回的确实是所指定的 $p_m$。特别读回的 $q=p_1$ 满足所列转换式；有限参数的 $q$ 不可能等于一，而 $q\ne1$ 时转换唯一可逆，故参数映射单射。$q=1/2$ 已由定理25.6的倍增方程排除；任何其他 $q$，若 $q=1$ 则对应 $\infty$，否则 $q/(q-1)$ 既不等于一，也只有在 $q=1/2$ 时才等于负一。因此每个允许的 $q$ 都有对应核。

检查统一公式的分母。若奇数 $m$ 满足 $q^m=(q-1)^m$，实数奇次幂的单射性给 $q=q-1$，不可能。若偶数 $m$ 满足该等式，则 $|q|=|q-1|$，平方后得 $q=1/2$，也被排除。因此每个 $D_m(q)\ne0$。当 $q\ne1$ 时，将 $t=q/(q-1)$ 代入定理25.7公式并约去 $(q-1)$ 的幂，得到所列统一式。当 $q=1$ 时，$D_m(1)=1$，统一式直接给 $p_m=1,c_{m,n}=-1$，与另行定义的形式参数核相同，不使用极限。证毕。

**定理 25.11（余边界、代数直和与单位障碍）。** 对有限参数定义 $d_m=1-t^m$，对形式参数 $\infty$ 定义 $d_m=-1$。则 $d_m\ne0$，并且
$$
c_{m,n}=\frac{d_md_n}{d_{m+n}}.
$$
因此这是正整数加法半群上的乘法余边界；这里该术语指所显示的公式。[^rro25-cocycle] 置 $u_m=v_m/d_m$，则
$$
u_m*_t u_n=u_{m+n}.
$$
作为不要求有单位的实代数，有同构
$$
(A,*_t)\cong\mathbb R[\mathbb T]\times X\mathbb R[X],
$$
其中第二因子为常数项为零的实多项式代数，两个因子的交叉乘积为零。整个 $A$ 不存在左单位或右单位，尽管 $\delta_{0_K}$ 是相位子代数 $V$ 的单位。

**证明。** 有限参数的公式由
$$
\frac{(1-t^m)(1-t^n)}{1-t^{m+n}}
=-\frac{(t^m-1)(t^n-1)}{t^{m+n}-1}
$$
得到；形式参数下 $(-1)(-1)/(-1)=-1$。全部 $d_m$ 非零已由参数域保证。故
$$
u_m*_t u_n
=\frac{c_{m,n}}{d_md_n}v_{m+n}
=\frac{v_{m+n}}{d_{m+n}}
=u_{m+n}.
$$
定理25.5的基经各个非零标量重标度后，$\{\pi_\theta\}\cup\{u_m\}$ 仍为基。定义线性映射
$$
\pi_\theta\longmapsto(b_\theta,0),\qquad
u_m\longmapsto(0,X^m).
$$
右边也是所列直积的基：两个坐标均只涉及有限形式和。因此该映射双射。相位基的乘法是群加法，正整数基的乘法是指数相加，而交叉乘积两侧都为零；逐对检查基向量，便知双射保持乘法。这也直接证明 $V,J$ 都是双侧理想，并给出代数直和，而非仅仅向量空间直和。

若 $a\in A$，将它作唯一有限展开
$$
a=\sum_\theta a_\theta\pi_\theta+\sum_{n\ge1}b_n v_n.
$$
则
$$
a*_t v_1=\sum_{n\ge1}b_nc_{n,1}v_{n+1},\qquad
v_1*_t a=\sum_{n\ge1}b_nc_{1,n}v_{n+1}.
$$
两者在基向量 $v_1$ 上的系数都为零，不可能等于 $v_1$。因此不存在任何左单位或右单位。另一方面 $\pi_0=\delta_{0_K}$ 与每个 $\pi_\theta$ 相乘给 $\pi_\theta$，确是 $V$ 的单位。上述抽象代数同构没有要求保持每个 $\delta_x$；定理25.10是在固定点质量基上的核相等分类，二者不混同。证毕。

**定理 25.12（非负系数边界恰为两个确定性核）。** 对本节的任意结合核，下列条件等价：所有 $P_{x,y}(w)$ 非负；每个 $P_{x,y}$ 都是一个点质量；参数属于 $\{0,\infty\}$。参数零的核在分裂和相位处，只有两个正号分裂输入的输出为正支，其余输入输出负支。形式参数 $\infty$ 的核在分裂和相位处，只有两个负号分裂输入的输出为负支，其余输入输出正支。和相位非分裂时二者都输出其唯一点。

**证明。** 假设全部点质量乘积的系数非负。由实际零切片 $P_{0_K,x_m^+}=\pi_{E_m}$，每个 $p_m$ 都属于 $[0,1]$。令 $q=p_1$。若 $0<q<1/2$，倍增递推给
$$
p_2=\frac{q^2}{2q-1}<0,
$$
矛盾。若 $1/2<q<1$，则
$$
p_2-1=\frac{(q-1)^2}{2q-1}>0,
$$
也矛盾。$q=1/2$ 对任何结合核均不可能。因此 $q=0$ 或 $q=1$，分别对应参数零与形式参数 $\infty$。

当 $t=0$ 时，所有 $\pi_{E_m}=\delta_{x_m^-}$。定理25.9中同号正输入输出正支，同号负输入输出负支；两个异号公式在所有正指标处均给正支系数零、负支系数一；含非分裂输入的分裂和相位输出为其负支切片。这正是所述默认负支规则。形式参数 $\infty$ 时，切片及异号输出均为正支，同号负输入仍被强制为负支，得到所述默认正支规则。因此两个参数都给点质量核，进而给非负系数核。任何点质量核显然非负，三者等价。

对其他参数，$q\notin\{0,1\}$，所以 $P_{0_K,x_1^+}$ 已有两个非零系数，不是点质量。若 $q$ 在 $[0,1]$ 之外，该切片直接含负系数；若 $q$ 在其内部，则上面的倍增计算说明第二个分裂零切片含负系数。因此其余核确实需要允许负系数。证毕。

**定理 25.13（一个显式非 Dirac 核）。** 参数 $t=2$ 给出全 $K$ 上的归一化实有符号结合核，并满足
$$
P^{(2)}_{0_K,x_1^+}
=P^{(2)}_{0_K,x_1^-}
=2\delta_{x_1^+}-\delta_{x_1^-},
$$
$$
P^{(2)}_{x_1^+,x_1^+}=\delta_{x_2^+},\qquad
P^{(2)}_{x_1^-,x_1^-}=\delta_{x_2^-},
$$
$$
P^{(2)}_{x_1^+,x_1^-}
=P^{(2)}_{x_1^-,x_1^+}
=\frac23\delta_{x_2^+}+\frac13\delta_{x_2^-}.
$$
因此精确闭图支撑与结合性并不单独强制 Dirac 输出，而附加系数非负性恰将全部核缩减为定理25.12的两个确定性核。

**证明。** 参数二避开禁止值，故定理25.9已经证明其在全载体上的存在、结合性和精确支撑。直接代入得
$$
p_1=2,\qquad p_2=\frac43,\qquad c_{1,1}=-\frac13.
$$
零切片遂为显示的两个系数，其和是 $2-1=1$，且负支系数为负一，所以不是点质量，也不是非负系数组合。同号公式直接来自定理25.9中已经逐项证明的强制支撑恒等式；异号公式代入 $m=n=1,t=2$ 给 $2/3$ 与 $1/3$。最后的非负性结论由定理25.12的参数穷尽推出。证毕。

[^rro25-graph]: *RECURSIVE_RELATIONAL_OBSERVATION*，固定提交 c74985438ae17d205509255934bbd3ecf1f94d71，定义16.0、16.3及定理16.4（包括单侧逼近与共同输入序列的完整证明），[固定文本](https://raw.githubusercontent.com/the-omega-institute/trureturing/c74985438ae17d205509255934bbd3ecf1f94d71/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md)。

[^rro25-phase]: *CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF*，固定提交 c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb，第371—372节，特别定理371.2、372.2—372.4，[固定文本](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md)。

[^rro25-affine]: Mathlib contributors, *Affine combinations*, 关于系数和为一的有限仿射组合及其与基点无关性的定义和恒等式，[数学文档](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/AffineSpace/Combination.html)。

[^rro25-algebra]: Mathlib contributors, *Monoid algebras*, 关于有限形式线性组合、加法群代数及有限卷积的定义，[数学文档](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MonoidAlgebra/Defs.html)。

[^rro25-cocycle]: Laurent Rigal and Pablo Zadunaisky, *Twisted semigroup algebras*, arXiv:1406.2985v2 (2014), §3.1，Definition 3.1.1、Remark 3.1.2及 Lemma 3.1.3；乘法余循环与余边界的术语参照，[正文](https://arxiv.org/html/1406.2985v2#S3.SS1)。

## 追加锚（本行以下为增补区）
## 26. Weakly almost periodic Zeckendorf observations and the phase quotient

**definition 26.0 (Carrier, observations, and one-sided compactness classes).** Put
$$
\mathbb N_0=\{0,1,\ldots\},\qquad
G_0=1,\quad G_1=2,\quad G_{\ell+2}=G_{\ell+1}+G_\ell,\qquad
\phi=\frac{1+\sqrt5}{2},\quad \alpha=\phi^{-1}.
$$
Use the low-to-high digit carrier and its metric
$$
K=\{x\in\{0,1\}^{\mathbb N_0}:x_jx_{j+1}=0\text{ for every }j\},\qquad
d_K(x,y)=\sum_{j\ge0}2^{-j-1}|x_j-y_j|.
$$
Here $Z(n)$ is the unique finite legal Zeckendorf expansion of $n$, padded by zeros, so that $n=\sum_jG_jZ(n)_j$. Write
$$
\mathbb T=\mathbb R/\mathbb Z,\qquad
\rho([s],[t])=\min_{k\in\mathbb Z}|s-t-k|,\qquad
F(x)=\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j,\qquad H(x)=[F(x)].
$$
These are the carrier and phase conventions of Definition 16.0 and the Zeckendorf volume, Definition 371.1. ([RECURSIVE_RELATIONAL_OBSERVATION.md](https://raw.githubusercontent.com/the-omega-institute/trureturing/c74985438ae17d205509255934bbd3ecf1f94d71/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md), Definition 16.0, pinned commit `c74985438ae17d205509255934bbd3ecf1f94d71`; [CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md), Definition 371.1, pinned commit `c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb`.)

Fix a scalar field $\mathbb F\in\{\mathbb R,\mathbb C\}$. Let
$$
B_{\mathbb F}=\ell^\infty(\mathbb N_0,\mathbb F),\qquad
(S^ka)(n)=a(n+k),\qquad
\mathcal O(a)=\{S^ka:k\in\mathbb N_0\}.
$$
A sequence $a\in B_{\mathbb F}$ is AP when $\mathcal O(a)$ has compact norm closure. It is WAP when $\mathcal O(a)$ has compact closure for the Banach weak topology $\sigma(B_{\mathbb F},B_{\mathbb F}^*)$, where the dual is taken over $\mathbb F$. WAP does not mean relative compactness for pointwise convergence or for $\sigma(\ell^\infty,\ell^1)$. For $f\in C(K,\mathbb F)$ define $a_f(n)=f(Z(n))$. All translation classes in this section use nonnegative translates, including the zeroth translate.

**Assumption 26.1 (Established structure of the fixed carrier).** Use the following published carrier facts. The space $K$ is compact, $Z(\mathbb N_0)$ is dense, and $H$ is a continuous surjection satisfying
$$
H(Z(n))=[n\phi].
$$
Its nonsingleton fibers are exactly
$$
E_m=[-m\phi],\qquad
H^{-1}(\{E_m\})=\{x_m^-,x_m^+\}\quad(m\ge1).
$$
Every other fiber is a singleton; in particular $H^{-1}(\{[n\phi]\})=\{Z(n)\}$ for $n\ge0$. The orientation is
$$
x_1^+=u=(10)^\infty,\qquad x_1^-=v=(01)^\infty.
$$
For each $m$, if $\epsilon_k\to0$ with a fixed strict sign and $H(y_k)=E_m+[\epsilon_k]$, then
$$
y_k\longrightarrow x_m^+\ \text{if }\epsilon_k>0,\qquad
y_k\longrightarrow x_m^-\ \text{if }\epsilon_k<0.
$$
This holds for arbitrary choices of the lifts $y_k$, including lifts over other split phases. There is a continuous map $T:K\to K$ with
$$
TZ(n)=Z(n+1),\qquad H(Tx)=H(x)+[\phi],\qquad Tu=Tv=Z(0).
$$
These facts are the conclusions of the Zeckendorf volume, theorems 371.2, 372.2–372.4, 375.2–375.3, 381.2, and 382.1, with the oriented labels of Definition 381.1 and Definition 16.3. ([CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md), sections 371–375 and 381–382, specifically theorems 371.2, 372.2–372.4, 375.2–375.3, 381.2 and 382.1 and Definition 381.1, pinned commit `c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb`; [RECURSIVE_RELATIONAL_OBSERVATION.md](https://raw.githubusercontent.com/the-omega-institute/trureturing/c74985438ae17d205509255934bbd3ecf1f94d71/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md), Definition 16.3, pinned commit `c74985438ae17d205509255934bbd3ecf1f94d71`.)

**theorem 26.2 (Explicit full-state double limits at every split phase).** For $m\ge1$ define
$$
r_m=\min\{r\in\mathbb N_0:G_{2r+1}\ge m\},\qquad
A_i^{(m)}=G_{2(i+r_m)+1}-m,\qquad B_j=G_{2j}\quad(i,j\ge0).
$$
These are nonnegative integer inputs. For every fixed $i$ and every fixed $j$, respectively,
$$
\lim_{j\to\infty}Z(A_i^{(m)}+B_j)=Z(A_i^{(m)}),\qquad
\lim_{i\to\infty}Z(A_i^{(m)}+B_j)=T^{B_j}x_m^+.
$$
Both iterated limits exist in the full space $K$, and their orientations are
$$
\lim_{i\to\infty}\lim_{j\to\infty}Z(A_i^{(m)}+B_j)=x_m^+,\qquad
\lim_{j\to\infty}\lim_{i\to\infty}Z(A_i^{(m)}+B_j)=x_m^-.
$$
Consequently every $f\in C(K,\mathbb F)$ satisfies
$$
\lim_{i\to\infty}\lim_{j\to\infty}a_f(A_i^{(m)}+B_j)=f(x_m^+),\qquad
\lim_{j\to\infty}\lim_{i\to\infty}a_f(A_i^{(m)}+B_j)=f(x_m^-).
$$
The full-lift convergence used here is the arbitrary-lift statement of theorem 382.1, not merely a lowest-digit assertion. ([CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md](https://raw.githubusercontent.com/the-omega-institute/trureturing/c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb/docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ZECKENDORF.md), theorem 382.1, including its arbitrary-lift one-sided convergence statement and proof, pinned commit `c4ef9baf3444a8e1992f6859eecc64e5faa6e0cb`.)

**Proof.** The positive Fibonacci recurrence makes $G_\ell$ strictly increasing and unbounded, so $r_m$ exists and $A_i^{(m)}\ge0$. Also $B_j\ge1$. First establish the exact signed error
$$
\phi G_\ell-G_{\ell+1}=(-1)^{\ell+1}\alpha^{\ell+2}.
$$
The left-hand sequence satisfies the Fibonacci recurrence. The right-hand sequence does also, because $1-\alpha=\alpha^2$. Their initial values agree:
$$
\phi-2=-\alpha^2,\qquad 2\phi-3=\alpha^3.
$$
Induction therefore proves the identity. Taking classes modulo one gives
$$
H(Z(A_i^{(m)}))=E_m+[\alpha^{2(i+r_m)+3}],\qquad
H(Z(B_j))=[-\alpha^{2j+2}].
$$
The first offset is strictly positive and tends to zero. Assumption 26.1 therefore yields
$$
Z(A_i^{(m)})\longrightarrow x_m^+.
$$
On the other hand $Z(B_j)$ has its only nonzero digit at position $2j$. Thus every fixed initial segment is eventually zero, and
$$
Z(B_j)\longrightarrow Z(0).
$$

Induction from $TZ(n)=Z(n+1)$ gives $T^hZ(n)=Z(n+h)$ for every nonnegative integer $h$. Fixing $i$ and using continuity of the single fixed iterate $T^{A_i^{(m)}}$ proves
$$
Z(A_i^{(m)}+B_j)=T^{A_i^{(m)}}Z(B_j)
\longrightarrow T^{A_i^{(m)}}Z(0)=Z(A_i^{(m)}).
$$
Fixing $j$ instead and using the single fixed iterate $T^{B_j}$ proves
$$
Z(A_i^{(m)}+B_j)=T^{B_j}Z(A_i^{(m)})
\longrightarrow T^{B_j}x_m^+.
$$
Taking the outer limit in the first identity already gives $x_m^+$.

For the second outer limit, the exact forward-iterate rule is
$$
T^hx_m^\pm=
\begin{cases}
x_{m-h}^\pm,&0\le h<m,\\
Z(h-m),&h\ge m.
\end{cases}
$$
Indeed, for $h<m$, choose any lifts of $E_m\pm[\epsilon_k]$ with $\epsilon_k>0$ tending to zero. They converge to $x_m^\pm$. Their images under $T^h$ have phases $E_{m-h}\pm[\epsilon_k]$, and hence converge to $x_{m-h}^\pm$. Continuity and uniqueness of limits give the first case. For $h\ge m$, semiconjugacy gives the phase $[(h-m)\phi]$, whose fiber is the singleton $\{Z(h-m)\}$, proving the second case.

Since $B_j\to\infty$, eventually
$$
T^{B_j}x_m^+=Z(B_j-m).
$$
For those indices, $B_j-m$ is a nonnegative integer and
$$
H(Z(B_j-m))=E_m+[-\alpha^{2j+2}].
$$
These phases approach from the strict negative side. The arbitrary-lift convergence in Assumption 26.1 gives $Z(B_j-m)\to x_m^-$. The finitely many indices with $B_j<m$ cause no loss of any inner limit: their values are explicitly $x_{m-B_j}^+$ by the forward-iterate rule. This proves the second full-state iterated limit.

For clarity, the seam case has $r_1=0$ and the exact digit identities
$$
A_i^{(1)}=G_{2i+1}-1=\sum_{r=0}^{i}G_{2r},\qquad
B_j-1=G_{2j}-1=\sum_{r=0}^{j-1}G_{2r+1}.
$$
For the first identity the base case is $G_0=G_1-1$, and adding $G_{2i+2}$ proves the next case by the recurrence. For the second identity the case $j=0$ is the empty sum; adding $G_{2j+1}$ again gives the next case. These sums are legal digit expansions, so
$$
Z(A_i^{(1)})=(10)^{i+1}0^\infty\longrightarrow u,\qquad
Z(B_j-1)=(01)^j0^\infty\longrightarrow v,\qquad
T^{B_j}u=Z(B_j-1).
$$
For general $m$ the construction is precisely
$$
A_i^{(m)}=A_{i+r_m}^{(1)}-(m-1).
$$
The truncation by $r_m$ is what makes every input nonnegative; no inverse iterate of $T$ is used. Finally, continuity of $f$ transports every inner limit and then each outer limit to the stated scalar limits. The witnesses therefore work for any continuous function separating the chosen pair. $\square$

**theorem 26.3 (Necessary Banach-weak double-limit implication).** Let $a\in B_{\mathbb F}$ be WAP, and let $P_i,Q_j\in\mathbb N_0$. Suppose that each inner limit exists and that both outer limits below exist. Then
$$
\lim_{i\to\infty}\lim_{j\to\infty}a(P_i+Q_j)
=
\lim_{j\to\infty}\lim_{i\to\infty}a(P_i+Q_j).
$$
This is the necessary direction of Grothendieck's double-limit criterion. Its general function-space hypotheses are a topological space $X$, a dense subset $X_0$, and a bounded family in $C_b(X)$ with the uniform norm; here take $X=X_0=\mathbb N_0$ discrete and the family $\mathcal O(a)$, whose elements have norm at most $\|a\|_\infty$. Grothendieck's original Proposition 7 also explicitly allows semigroups with continuous left and right translations. Sources: A. Grothendieck, *Critères de compacité dans les espaces fonctionnels généraux*, American Journal of Mathematics 74 (1952), 168–186, theorem 6 and Proposition 7; I. Ben Yaacov, *Model theoretic stability and definability of types, after A. Grothendieck*, Fact 2. (A. Grothendieck, [Critères de compacité dans les espaces fonctionnels généraux](https://webusers.imj-prg.fr/~leila.schneps/grothendieckcircle/AG/AG-6.pdf), American Journal of Mathematics 74 (1952), 168–186, theorem 6 and Proposition 7; I. Ben Yaacov, [Model theoretic stability and definability of types, after A. Grothendieck](https://math.univ-lyon1.fr/~begnac/articles/Grothendieck.pdf), Fact 2, p. 1.)

**Proof.** Write $r_i=S^{P_i}a$ and let $W$ be the weak closure of $\mathcal O(a)$. By hypothesis $W$ is weakly compact, so the sequence considered as a net has a subnet
$$
r_{i_\lambda}\longrightarrow r\in W
\quad\text{in }\sigma(B_{\mathbb F},B_{\mathbb F}^*).
$$
For $n\in\mathbb N_0$, evaluation $\delta_n(b)=b(n)$ is an element of $B_{\mathbb F}^*$ of norm one. Banach–Alaoglu gives an independently chosen subnet
$$
\delta_{Q_{j_\mu}}\longrightarrow\Lambda
\quad\text{in }\sigma(B_{\mathbb F}^*,B_{\mathbb F}),
$$
inside the dual unit ball. Set
$$
p_i=\lim_{j\to\infty}a(P_i+Q_j),\qquad
q_j=\lim_{i\to\infty}a(P_i+Q_j).
$$
For each fixed $i$, the scalar limit along the full $j$-sequence exists, hence the weak-star subnet gives $p_i=\Lambda(r_i)$. For each fixed $j$, the scalar limit along the full $i$-sequence exists, hence the weak subnet gives $q_j=\delta_{Q_j}(r)$. The existing outer limits can now be computed along the respective subnets:
$$
\lim_{i\to\infty}p_i
=\lim_\lambda\Lambda(r_{i_\lambda})
=\Lambda(r)
=\lim_\mu\delta_{Q_{j_\mu}}(r)
=\lim_{j\to\infty}q_j.
$$
Only evaluation with one argument fixed has been used. In particular, the proof does not assume joint continuity of a varying vector–functional pairing, or the existence of weakly convergent subsequences. The compactness hypothesis is Banach weak compactness, not compactness of a bounded pointwise closure. The proof applies over either scalar field. $\square$

**theorem 26.4 (Classification of continuous observations).** For every $f\in C(K,\mathbb F)$ the following conditions are equivalent:
$$
\begin{aligned}
&a_f\text{ is WAP};\\
&a_f\text{ is AP};\\
&f(x_m^-)=f(x_m^+)\quad\text{for every }m\ge1;\\
&\text{there exists a unique }g\in C(\mathbb T,\mathbb F)
  \text{ such that }f=g\circ H.
\end{aligned}
$$
For complex observations the WAP condition is also equivalent to WAP for both real and imaginary coordinate sequences; the analogous statement holds for AP.

**Proof.** Suppose first that $a_f$ is WAP. For any fixed $m$, theorem 26.2 provides actual nonnegative integer sequences whose two iterated scalar limits are $f(x_m^+)$ and $f(x_m^-)$. Theorem 26.3 forces them to agree. Thus $f$ is constant on every double fiber. Since every remaining fiber is a singleton, it is constant on every fiber of $H$.

Define $g(\theta)$ to be this common value on $H^{-1}(\{\theta\})$. Surjectivity makes this definition possible and gives uniqueness. We verify continuity rather than just set-theoretic factorization. The continuous map $H$ from compact $K$ to Hausdorff $\mathbb T$ is closed: the image of a closed subset of $K$ is compact, hence closed. It is therefore a quotient map. Explicitly, for every closed $D\subseteq\mathbb F$,
$$
g^{-1}(D)=H(f^{-1}(D)).
$$
The right-hand side is compact and closed in $\mathbb T$. Thus $g$ is continuous. Conversely, any factorization $f=g\circ H$ plainly makes the two values on every double fiber equal.

Now suppose $f=g\circ H$ with $g$ continuous. Define
$$
\Phi_g:\mathbb T\longrightarrow B_{\mathbb F},\qquad
\Phi_g(\theta)=\bigl(g(\theta+[n\phi])\bigr)_{n\ge0}.
$$
The map is well-defined because $g$ is bounded. Given $\epsilon>0$, uniform continuity of $g$ supplies $\delta>0$ such that $\rho(s,t)<\delta$ implies $|g(s)-g(t)|<\epsilon$. Translation invariance of $\rho$ then gives
$$
\rho(\theta,\eta)<\delta
\quad\Longrightarrow\quad
\|\Phi_g(\theta)-\Phi_g(\eta)\|_\infty\le\epsilon.
$$
Hence $\Phi_g$ is norm-continuous, and its image is norm-compact. Since
$$
S^ka_f=\Phi_g([k\phi])\qquad(k\ge0),
$$
this compact image contains the translation orbit and its norm closure. Therefore $a_f$ is AP.

Finally, if an orbit has compact norm closure $C$, the identity from $C$ with its norm topology to $B_{\mathbb F}$ with its weak topology is continuous. Its image is weakly compact and, since the weak topology is Hausdorff, weakly closed. It contains the weak closure of the orbit, which is consequently compact. Thus AP implies WAP and the four conditions are equivalent.

Everything in the argument holds separately over $\mathbb R$ and $\mathbb C$. In the complex case, equality of the two values of $f$ on every split fiber is equivalent to those equalities for both $\operatorname{Re}f$ and $\operatorname{Im}f$. Applying the already proved real and complex classifications establishes the coordinate assertions. No minimal-flow theorem or invertibility of $T$ is required. $\square$

**theorem 26.5 (Finite Hausdorff observations and the required scalar coordinates).** Let $Y$ be Hausdorff and $q:K\to Y$ continuous with finite image $D=q(K)$. Let $(\psi_\lambda:D\to\mathbb F)_{\lambda\in\Lambda}$ jointly separate points of $D$, meaning that distinct points have different values for at least one coordinate. Then
$$
\bigl(\psi_\lambda(q(Z(n)))\bigr)_{n\ge0}
\text{ is WAP for every }\lambda
\quad\Longleftrightarrow\quad
q\text{ is constant}.
$$
The same equivalence holds with AP in place of WAP. A single injective real-valued labelling of $D$ suffices.

**Proof.** A finite Hausdorff space is discrete: each singleton is closed, and its complement, being a finite union of closed singletons, is also closed. Thus every map $\psi_\lambda$ on $D$ is continuous. The co-restriction $q:K\to D$ is continuous, so $f_\lambda=\psi_\lambda\circ q$ belongs to $C(K,\mathbb F)$.

Under the WAP hypothesis, theorem 26.4 gives $f_\lambda=g_\lambda\circ H$ with $g_\lambda$ continuous. Since $H$ is onto,
$$
g_\lambda(\mathbb T)=f_\lambda(K)=\psi_\lambda(D),
$$
which is finite. The circle is connected, being the continuous image of the connected interval $[0,1]$. Its continuous image under $g_\lambda$ is therefore connected. A finite Hausdorff connected space has only one point, so every $f_\lambda$ is constant. If $q(x)\ne q(y)$, point separation would give a coordinate with $f_\lambda(x)\ne f_\lambda(y)$, a contradiction. Therefore $q$ is constant. The converse follows because a constant sequence has a singleton translation orbit. Theorem 26.4 identifies AP and WAP for each of these continuous scalar observations.

To obtain one scalar coordinate, assign distinct real numbers to the finitely many elements of $D$. This is a continuous injection on $D$; no scalar embedding of all of $Y$ is needed. If coordinates are instead prescribed as continuous functions on $Y$, their restrictions must jointly separate $D$. Hausdorffness alone is not being used to assert such a global scalar representation.

Both qualifications are necessary. Without separation, take the nonconstant continuous observation $q(x)=x_0$ but only the constant scalar coordinate: that coordinate gives a constant sequence. Without continuity on $K$, take
$$
q_0(x)=\mathbf 1_{\{u\}}(x).
$$
It is nonconstant, while $q_0(Z(n))=0$ for every $n$, because $u$ is not a finite padded word. Moreover $Z(A_i^{(1)})\to u$ while all those values are zero and $q_0(u)=1$, proving the discontinuity. Thus no constancy conclusion for arbitrary discontinuous finite observations follows. $\square$

**theorem 26.6 (The phase observation algebra and deterministic closed-graph readout).** Define
$$
\mathcal R:C(K,\mathbb F)\longrightarrow B_{\mathbb F},\quad
\mathcal Rf=a_f,\qquad
H^*g=g\circ H,\qquad
\mathscr A_{\mathbb F}=H^*C(\mathbb T,\mathbb F).
$$
Both $\mathcal R$ and $H^*$ are isometries. The space $\mathscr A_{\mathbb F}$ is a closed unital algebra, closed under conjugation when $\mathbb F=\mathbb C$, and
$$
\begin{aligned}
\mathcal R(C(K,\mathbb F))\cap\operatorname{WAP}(\mathbb N_0,\mathbb F)
&=\mathcal R(C(K,\mathbb F))\cap\operatorname{AP}(\mathbb N_0,\mathbb F)\\
&=\mathcal R(\mathscr A_{\mathbb F}).
\end{aligned}
$$
The equivalence relation detected by all these continuous WAP observations is exactly the phase relation:
$$
\bigl(\forall f\in\mathscr A_{\mathbb F},\ f(x)=f(y)\bigr)
\quad\Longleftrightarrow\quad H(x)=H(y).
$$

Retain the closed addition graph
$$
\Gamma=\overline{\{(Z(n),Z(k),Z(n+k)):n,k\in\mathbb N_0\}}\subseteq K^3,\qquad
\Gamma(x,y)=\{z:(x,y,z)\in\Gamma\}.
$$
For $f\in C(K,\mathbb F)$, the following are also equivalent to the conditions of theorem 26.4: $f$ has one common value on every nonempty output set $\Gamma(x,y)$; and there exists a continuous $D_f:K^2\to\mathbb F$ satisfying
$$
D_f(Z(n),Z(k))=f(Z(n+k))\qquad(n,k\ge0).
$$
When these conditions hold, this extension is unique and equals
$$
D_f(x,y)=g(H(x)+H(y)).
$$
The graph input-fiber classification used below is theorem 16.4. ([RECURSIVE_RELATIONAL_OBSERVATION.md](https://raw.githubusercontent.com/the-omega-institute/trureturing/c74985438ae17d205509255934bbd3ecf1f94d71/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION.md), theorem 16.4, complete statement and proof of the closed-addition-graph input-fiber classification, pinned commit `c74985438ae17d205509255934bbd3ecf1f94d71`.)

**Proof.** Density of the finite core and continuity give
$$
\|\mathcal Rf\|_\infty=\sup_{n\ge0}|f(Z(n))|=\sup_{x\in K}|f(x)|.
$$
Surjectivity of $H$ similarly gives $\|H^*g\|_\infty=\|g\|_\infty$. Completeness of $C(\mathbb T,\mathbb F)$ and this isometry make its range closed. Pullback preserves constants, sums, products, and, over $\mathbb C$, conjugation. This proves the algebra assertions. The intersection identity is exactly theorem 26.4 applied to every $f$.

Equal phases give equal values for all pullbacks. Conversely, if $H(x)\ne H(y)$, the real continuous function $g(\theta)=\rho(\theta,H(x))$ gives
$$
(g\circ H)(x)=0,\qquad (g\circ H)(y)>0.
$$
It belongs to the real algebra and, by regarding its values as complex, to the complex algebra. This proves the asserted equivalence relation.

For any $x,y$, density supplies sequences of core inputs converging to $x,y$. Compactness of $K$ supplies a convergent subsequence of their sums, showing that $\Gamma(x,y)$ is nonempty. Continuity of $H$ on a convergent core triple gives
$$
\Gamma(x,y)\subseteq H^{-1}(\{H(x)+H(y)\}).
$$
In addition, theorem 16.4, with its first input $Z(0)$ having an unsplit phase, gives
$$
\Gamma(Z(0),x_m^+)=\{x_m^+,x_m^-\}\qquad(m\ge1).
$$
Thus constancy of $f$ on every graph output set forces equality on every split pair, and theorem 26.4 gives $f=g\circ H$. In the reverse direction, the displayed phase containment makes every value $f(z)$ on $\Gamma(x,y)$ equal to $g(H(x)+H(y))$.

If the phase factorization holds, the displayed formula for $D_f$ is continuous and has the required core values. Conversely, suppose such a continuous extension exists. For any $(x,y,z)\in\Gamma$, metrizability gives a sequence of core triples converging to it. Continuity of $D_f$ and $f$ yields $D_f(x,y)=f(z)$. Hence $f$ is constant on every output set and therefore factors through $H$. Any two continuous extensions agree on the dense set $Z(\mathbb N_0)^2$, so agree everywhere.

This scalar determinism for fixed full inputs does not assert that a binary operation can be recovered from the two scalar summaries alone. Indeed, let $g([t])=\cos(2\pi t)$ and $f=g\circ H$. Choose phases $[1/4]$ and $[3/4]$ for the first input and phase $[1/4]$ for the second. The two scalar input pairs are both $(0,0)$, whereas the prescribed outputs are respectively $-1$ and $1$. Surjectivity of $H$ realizes these choices in $K$. Thus no function of just those two scalar summaries can represent this $D_f$ on all inputs.

Finally, the intersection restriction is essential. Define $b(0)=1$ and $b(n)=0$ for $n\ge1$. Its nonnegative translation orbit is $\{b,0\}$, so it is AP under Definition 26.0. Nevertheless $b$ has no continuous extension along $Z$: since $G_{2j}\ge1$ and $Z(G_{2j})\to Z(0)$, such an extension would have values zero converging to its value one at $Z(0)$. Consequently the classification does not identify the full sequence spaces $\operatorname{WAP}(\mathbb N_0,\mathbb F)$ and $\operatorname{AP}(\mathbb N_0,\mathbb F)$. $\square$

**theorem 26.7 (Exact uniform distance to continuous phase observations).** For $f\in C(K,\mathbb F)$ put
$$
\Delta(f)=\sup_{m\ge1}|f(x_m^+)-f(x_m^-)|.
$$
Then
$$
\inf_{g\in C(\mathbb T,\mathbb F)}\|f-g\circ H\|_\infty
=
\inf_{b\in\mathcal R(\mathscr A_{\mathbb F})}\|a_f-b\|_\infty
=
\frac{\Delta(f)}2.
$$
In particular the sequence-space distance here is to the WAP observations already continuous on $K$, as identified in theorem 26.6, not an assertion about distance to all WAP sequences.

**Proof.** Write $d=\Delta(f)/2$. For every $g$ and every split pair, the triangle inequality gives
$$
|f(x_m^+)-f(x_m^-)|
\le |f(x_m^+)-g(E_m)|+|f(x_m^-)-g(E_m)|
\le2\|f-g\circ H\|_\infty.
$$
Taking the supremum over $m$ gives the lower bound $d$.

Fix $\epsilon>0$. For each $\theta\in\mathbb T$, choose a center $c_\theta\in\mathbb F$: use the value of $f$ on a singleton fiber, and the midpoint of its two values on a double fiber. Since every fiber has at most two points,
$$
|f(x)-c_\theta|\le d\qquad(H(x)=\theta).
$$
The set
$$
C_\theta=\{x\in K:|f(x)-c_\theta|\ge d+\epsilon\}
$$
is compact and disjoint from the fiber over $\theta$. Its image under $H$ is closed. Therefore
$$
U_\theta=\mathbb T\setminus H(C_\theta)
$$
is an open neighborhood of $\theta$, and every $x$ whose phase belongs to $U_\theta$ satisfies $|f(x)-c_\theta|<d+\epsilon$.

Choose a finite subcover $U_1,\ldots,U_N$ and the corresponding centers $c_1,\ldots,c_N$. For a nonempty closed set $C$, write $\rho(t,C)=\inf_{s\in C}\rho(t,s)$. Construct continuous weights by
$$
w_\ell(t)=
\begin{cases}
\rho(t,\mathbb T\setminus U_\ell),&U_\ell\ne\mathbb T,\\
1,&U_\ell=\mathbb T,
\end{cases}
\qquad
p_\ell(t)=\frac{w_\ell(t)}{\sum_{h=1}^Nw_h(t)}.
$$
Here distance to a nonempty closed set is continuous. An open neighborhood contains a positive-radius ball about each of its points, so the covering property makes the denominator positive everywhere. Thus the $p_\ell$ are continuous and nonnegative, their sum is one, and $p_\ell(t)>0$ implies $t\in U_\ell$. Set
$$
g_\epsilon(t)=\sum_{\ell=1}^Np_\ell(t)c_\ell.
$$
For $x\in K$, all positively weighted centers satisfy the preceding strict estimate at $t=H(x)$. Hence
$$
|f(x)-g_\epsilon(H(x))|
\le\sum_{\ell=1}^Np_\ell(H(x))|f(x)-c_\ell|
\le d+\epsilon.
$$
It follows that the infimum of the uniform error is at most $d+\epsilon$. Letting $\epsilon$ decrease to zero proves equality with $d$. This midpoint and convex-combination argument is valid over both $\mathbb R$ and $\mathbb C$. Finally, the isometry $\mathcal R$ from theorem 26.6 gives the equality with the stated sequence-space infimum. The proof constructs arbitrarily accurate approximants and does not assert attainment of the infimum. $\square$

## 追加锚（本行以下为增补区）
## 27. Absolute summability, exact norms, and the compact digit topology

**Assumption 27.0 (Fixed carrier, exact graph, and classified finite multiplication).** Retain the carrier, phase map, oriented exceptional fibers, and finite addition graph of Definition 25.0, together with the exact-fiber and exact-graph hypotheses of Assumption 25.1. In particular,
$$
\Gamma=\overline{\{(Z(a),Z(b),Z(a+b)):a,b\in\mathbb N\}}^{\,K^3}.
$$
Fix
$$
t\in\Lambda=(\mathbb R\setminus\{-1,1\})\sqcup\{\infty\},
$$
and use the finite multiplication and kernel of Definitions 25.2 and 25.8 and theorems 25.6–25.9. Thus the product on $A=\mathbb R^{(K)}$ is associative and commutative, each row has coefficient sum one and support contained in the exact set $\Gamma(x,y)$, and
$$
P^{(t)}_{Z(a),Z(b)}=\delta_{Z(a+b)}\qquad(a,b\in\mathbb N).
$$
The symbols $p_m,c_{m,n},\pi_\theta,v_m$ always have their values for this fixed parameter. The parameter $\infty$ remains a separate formal symbol.

**definition 27.1 (Absolute sums and norm constants).** For a nonnegative family $(h_s)_{s\in S}$ over an arbitrary set, define
$$
\sum_{s\in S}h_s=\sup_{F\subseteq S,\ F\text{ finite}}\sum_{s\in F}h_s.
$$
Define
$$
\ell^1(S)=\left\{a:S\to\mathbb R:\|a\|_1:=\sum_{s\in S}|a(s)|<\infty\right\}.
$$
No support restriction is imposed in this definition. A subscript ${\mathrm d}$ on a topological set denotes its underlying set equipped with the discrete topology. Thus $\ell^1(K_{\mathrm d})$ and $\ell^1(\mathbb T_{\mathrm d})$ use counting sums, not integration against a measure associated with their original compact topologies.[^rro27-l1]

For a finite signed atomic measure, use the total variation norm
$$
\left\|\sum_{w\in F}a_w\delta_w\right\|_{\mathrm{TV}}=\sum_{w\in F}|a_w|,
$$
where the points of $F$ are distinct. This convention has no factor of one half. Define
$$
\rho_t=\begin{cases}
|t|,&t\ne\infty,\ |t|<1,\\
|t|^{-1},&t\ne\infty,\ |t|>1,\\
0,&t=\infty,
\end{cases}
\qquad
C_t=\frac{1+\rho_t}{1-\rho_t}.
$$
Consequently,
$$
0\le\rho_t<1,\qquad
C_t=\frac{1+|t|}{|1-|t||}\quad(t\ne\infty),\qquad C_\infty=1.
$$

**theorem 27.2 (Exact row variation and exact finite bilinear norm).** For every parameter in Assumption 27.0,
$$
\max_{x,y\in K}\|P^{(t)}_{x,y}\|_{\mathrm{TV}}=C_t.
$$
The maximum is attained at $(0_K,x_1^+)$ for every finite $t\ge0$ in the parameter domain, at $(x_1^+,x_1^-)$ for every $t<0$ in the parameter domain, and at $(0_K,0_K)$ for the formal parameter $\infty$. Moreover,
$$
\sup_{\substack{a,b\in A\\\|a\|_1\le1,\ \|b\|_1\le1}}\|a*_t b\|_1=C_t.
$$

**Proof.** We first bound every row. When at least one input is nonexceptional, theorem 25.9 gives the output $\pi_{H(x)+H(y)}$. A nonexceptional output phase gives a Dirac measure and hence norm one. At an exceptional phase, for finite $t$ and $r=|t|$,
$$
\|\pi_{E_m}\|_{\mathrm{TV}}
=|p_m|+|1-p_m|
=\frac{1+r^m}{|1-t^m|}.
$$
If $t<0$ and $m$ is odd, this expression is one. In every other finite-parameter case it equals
$$
\frac{1+\rho_t^m}{1-\rho_t^m}\le\frac{1+\rho_t}{1-\rho_t}=C_t.
$$
Here the inequality follows from $0\le\rho_t^m\le\rho_t<1$ and the monotonicity of $(1+u)/(1-u)$ on $[0,1)$. This also covers $t=0$. For the formal parameter, every $\pi_\theta$ is a Dirac measure.

Two exceptional inputs with the same sign give a Dirac measure by theorem 25.9, for all indices and every parameter. It remains to bound the two mixed-sign types. For finite $t$, put
$$
M_{m,n}(t)=\|P^{(t)}_{x_m^+,x_n^-}\|_{\mathrm{TV}}
=\frac{|t|^n|t^m-1|+|t^n-1|}{|t^{m+n}-1|}.
$$
The reversed-sign type has norm $M_{n,m}(t)$, as is seen directly from its formula in theorem 25.9. For $t=0$, the mixed row is $\delta_{x_{m+n}^-}$, so its norm is one. For $t>0$, both mixed coefficients are nonnegative: when $t<1$, their relevant factors and denominator have the corresponding negative signs, and when $t>1$ all those factors are positive. Their sum is one, so again $M_{m,n}(t)=1$.

Suppose next that $t=-r$ with $0<r<1$. Write $u=r^m$ and $v=r^n$. Direct substitution into the two mixed coefficients gives the exhaustive parity cases
$$
M_{m,n}(-r)=\begin{cases}
1,&n\text{ even},\\
\dfrac{1+2v-uv}{1+uv},&n\text{ odd},\ m\text{ even},\\
\dfrac{1+2v+uv}{1-uv},&n\text{ odd},\ m\text{ odd}.
\end{cases}
$$
Indeed, $t^m-1$, $t^n-1$, and $t^{m+n}-1$ are all negative, so the second mixed coefficient is positive and the first has the sign of $t^n$. This establishes the first case and gives the two displayed absolute-value expressions in the remaining cases. Since $0<u,v\le r<1$, the even-$m$, odd-$n$ case satisfies
$$
\frac{1+2v-uv}{1+uv}
=1+\frac{2v(1-u)}{1+uv}
\le1+2r
\le\frac{1+r}{1-r}.
$$
The odd-$m$, odd-$n$ case satisfies
$$
\frac{1+2v+uv}{1-uv}
=1+\frac{2v(1+u)}{1-uv}
\le1+\frac{2r(1+r)}{1-r^2}
=\frac{1+r}{1-r}.
$$
Thus every parity case is bounded by $C_t$ when $-1<t<0$.

For every nonzero admissible finite parameter, direct multiplication of numerator and denominator by $|t|^{m+n}$ gives
$$
M_{m,n}(t)=M_{n,m}(t^{-1}).
$$
More explicitly, the numerator of $M_{n,m}(t^{-1})$, after that multiplication, becomes
$$
|t^n-1|+|t|^n|t^m-1|.
$$
The denominator becomes $|t^{m+n}-1|$. Therefore all cases $t<-1$, including every parity combination, reduce to the preceding proof for $t^{-1}\in(-1,0)$, and $C_{t^{-1}}=C_t$. Swapping $m,n$ also bounds every reversed-sign row. For the formal parameter, both mixed rows are Dirac measures by theorem 25.9. These cases exhaust all input pairs.

For finite $t\ge0$, the actual zero slice gives
$$
\|P^{(t)}_{0_K,x_1^+}\|_{\mathrm{TV}}
=\|\pi_{E_1}\|_{\mathrm{TV}}
=\frac{1+t}{|1-t|}=C_t.
$$
For finite $t<0$, the actual first mixed pair gives, after cancelling the nonzero factor $t-1$,
$$
P^{(t)}_{x_1^+,x_1^-}
=\frac{t}{t+1}\delta_{x_2^+}+\frac1{t+1}\delta_{x_2^-}.
$$
Since $t\ne-1$ and the two output points are distinct, its norm is
$$
\frac{|t|+1}{|t+1|}=\frac{1+|t|}{|1-|t||}=C_t.
$$
For $\infty$, the row at $(0_K,0_K)$ is $\delta_{0_K}$ and attains $C_\infty=1$.

Finally, finite bilinearity and the row bound give
$$
\|a*_t b\|_1
\le\sum_{x,y}|a(x)|\,|b(y)|\,\|P^{(t)}_{x,y}\|_1
\le C_t\|a\|_1\|b\|_1.
$$
The two point masses associated with each attaining pair have norm one, and their product has norm $C_t$. Hence the bilinear norm is exactly $C_t$. QED.

**theorem 27.3 (The actual discrete completion).** For every set $S$, each member of $\ell^1(S)$ has at most countable support. The normed space $\ell^1(S)$ is complete, and $\mathbb R^{(S)}$ is dense in it. In particular, the completion of $A$ in the point-mass coefficient norm is precisely $\ell^1(K_{\mathrm d})$.

**Proof.** Let $a\in\ell^1(S)$. For every integer $j\ge1$, the set
$$
S_j=\{s\in S:|a(s)|\ge1/j\}
$$
is finite. Otherwise finite subsets of arbitrarily large cardinality would make the defining supremum for $\|a\|_1$ infinite. Every nonzero coefficient belongs to some $S_j$, so
$$
\operatorname{supp}(a)=\bigcup_{j\ge1}S_j
$$
is at most countable. The sum defining the norm is therefore the usual absolutely convergent sum on this support, with its value independent of enumeration.

For every $\epsilon>0$, the definition by finite suprema supplies a finite $F\subseteq S$ with
$$
\sum_{s\in F}|a(s)|>\|a\|_1-\epsilon.
$$
Taking finite suprema on the complement gives
$$
\|a-a\mathbf1_F\|_1=\sum_{s\notin F}|a(s)|<\epsilon.
$$
This proves finite-support density.

For completeness, let $(a_j)$ be a Cauchy sequence. Each coordinate is Cauchy because
$$
|a_j(s)-a_k(s)|\le\|a_j-a_k\|_1.
$$
Let $a(s)$ be its limit. The Cauchy sequence has bounded norms, say bounded by $M$. For every finite $F$,
$$
\sum_{s\in F}|a(s)|=\lim_{j\to\infty}\sum_{s\in F}|a_j(s)|\le M.
$$
Thus $a\in\ell^1(S)$. Given $\epsilon>0$, take $N$ such that $\|a_j-a_k\|_1<\epsilon$ for $j,k\ge N$. Fixing $j\ge N$, taking the limit in each finite coordinate sum, and then taking its finite supremum yields
$$
\|a_j-a\|_1\le\epsilon.
$$
Therefore $a_j\to a$ in norm. The triangle inequality, homogeneity, and definiteness of the norm follow directly from its finite-supremum definition. QED.

**definition 27.4 (The convolution direct sum).** Put
$$
\mathcal G=\ell^1(\mathbb T_{\mathrm d}),\qquad
\mathcal S=\ell^1(\mathbb N_{>0}),\qquad
\mathcal B=\mathcal G\oplus_1\mathcal S.
$$
The products within the two summands are the discrete convolutions
$$
(f*_{\mathbb T}f')(\theta)=\sum_{\rho\in\mathbb T}f(\rho)f'(\theta-\rho),
$$
$$
(g*_{+}g')(k)=\sum_{\substack{m,n\ge1\\m+n=k}}g_mg'_n.
$$
An empty sum is zero; in particular, every product in $\mathcal S$ has first coordinate zero. Define
$$
(f,g)\diamond(f',g')=(f*_{\mathbb T}f',\ g*_{+}g'),\qquad
\|(f,g)\|_{\oplus}=\|f\|_1+\|g\|_1.
$$
Thus convolution is performed separately in the two summands, and cross products between the summands vanish. It is not pointwise multiplication of the sequences.[^rro27-ba]

**theorem 27.5 (Unique bounded multiplication, augmentation, and phase map).** There is a unique bounded bilinear extension of $*_t$ to
$$
B=\ell^1(K_{\mathrm d}).
$$
It is associative and commutative, has exact bilinear norm $C_t$ in the coefficient norm, and is given by the unconditionally convergent series
$$
a*_t b=\sum_{x,y\in K}a(x)b(y)P^{(t)}_{x,y}.
$$
In particular,
$$
(a*_t b)(w)=\sum_{x,y\in K}a(x)b(y)P^{(t)}_{x,y}(w),
$$
with the absolute-summability estimate
$$
\sum_{x,y,w\in K}|a(x)b(y)P^{(t)}_{x,y}(w)|
\le C_t\|a\|_1\|b\|_1.
$$
The maps
$$
\varepsilon(a)=\sum_{x\in K}a(x),\qquad
(H_{\#}a)(\theta)=\sum_{H(x)=\theta}a(x)
$$
are bounded linear maps of norm one, and
$$
\varepsilon(a*_t b)=\varepsilon(a)\varepsilon(b),\qquad
H_{\#}(a*_t b)=(H_{\#}a)*_{\mathbb T}(H_{\#}b).
$$
The phase map $H_{\#}:B\to\mathcal G$ is surjective.

With the equivalent norm
$$
\|a\|_{\mathrm{alg},t}=C_t\|a\|_1,
$$
the resulting algebra, denoted $B_t$, is a Banach algebra with a submultiplicative norm. The original coefficient norm itself is submultiplicative exactly for $t\in\{0,\infty\}$.

**Proof.** By theorem 27.3, the supports of $a$ and $b$ are at most countable. Their Cartesian product is at most countable, and the union of the finite row supports over these pairs is also at most countable. Moreover,
$$
\sum_{x,y}\|a(x)b(y)P^{(t)}_{x,y}\|_1
\le C_t\sum_{x,y}|a(x)|\,|b(y)|
=C_t\|a\|_1\|b\|_1.
$$
The last equality follows by taking suprema of finite rectangular sums of a nonnegative product family. Consequently the vector-valued series has arbitrarily small norm tails and converges in the complete space $B$, independently of its ordering. Expanding the row norms gives the stated absolute sum over $x,y,w$. Absolute convergence permits every regrouping used in the coordinate formula. Bounded coordinate evaluation shows that the coordinate formula agrees with the vector-valued sum.

The sum is bilinear and satisfies
$$
\|a*_t b\|_1\le C_t\|a\|_1\|b\|_1.
$$
In particular,
$$
\|a*_t b-a' *_t b'\|_1
\le C_t\bigl(\|a-a'\|_1\|b\|_1+\|a'\|_1\|b-b'\|_1\bigr).
$$
Choose finite-support sequences converging respectively to $a,b,c$. Their norms are bounded, their pairwise products converge by this inequality, and applying the inequality a second time shows that both bracketings of their triple products converge to the corresponding bracketings for $a,b,c$. The finite associativity identity therefore passes to the limit. Finite commutativity passes to the limit in the same way. Any bounded bilinear extension must agree on limits of finite-support pairs, proving uniqueness. The attaining point-mass pairs from theorem 27.2 still belong to $B$, so the extended bilinear norm remains exactly $C_t$.

The same absolute-sum argument applies to any discrete semigroup with rows $\delta_s*\delta_u=\delta_{su}$: every row has norm one, and semigroup associativity holds on the finite core. Applied to the group $\mathbb T_{\mathrm d}$ and the additive semigroup $\mathbb N_{>0}$, it proves that both convolutions in Definition 27.4 are associative bounded products satisfying
$$
\|f*_{\mathbb T}f'\|_1\le\|f\|_1\|f'\|_1,\qquad
\|g*_{+}g'\|_1\le\|g\|_1\|g'\|_1.
$$
Together with theorem 27.3 this also proves completeness and submultiplicativity for $\mathcal B$, since
$$
\|(f,g)\diamond(f',g')\|_{\oplus}
\le\|f\|_1\|f'\|_1+\|g\|_1\|g'\|_1
\le\|(f,g)\|_{\oplus}\|(f',g')\|_{\oplus}.
$$

Absolute summability gives
$$
|\varepsilon(a)|\le\|a\|_1,\qquad
\|H_{\#}a\|_1\le\sum_{\theta}\sum_{H(x)=\theta}|a(x)|=\|a\|_1.
$$
Both operator norms equal one by evaluation on $\delta_{0_K}$. On finite-support inputs, multiplicativity is theorem 25.3. Finite-support density and the established continuity of all the products and linear maps extend both identities to $B$.

For surjectivity, if $f\in\mathcal G$, the series
$$
a=\sum_{\theta\in\mathbb T}f(\theta)\pi_\theta
$$
converges absolutely in $B$, because theorem 27.2 bounds every $\|\pi_\theta\|_1$ by $C_t$. Since $H_{\#}\pi_\theta=\delta_\theta$, boundedness of $H_{\#}$ gives $H_{\#}a=f$.

Finally,
$$
\|a*_t b\|_{\mathrm{alg},t}
=C_t\|a*_t b\|_1
\le C_t^2\|a\|_1\|b\|_1
=\|a\|_{\mathrm{alg},t}\|b\|_{\mathrm{alg},t}.
$$
Completeness is unchanged by this positive scalar rescaling. Under the convention that a Banach-algebra norm is submultiplicative, this supplies such a norm.[^rro27-ba] If $t=0$ or $t=\infty$, then $C_t=1$, so the coefficient norm already suffices. Every other admissible parameter has $C_t>1$, and an attaining pair of norm-one point masses has product norm greater than one. Thus the unscaled coefficient norm is not submultiplicative in those cases. QED.

**theorem 27.6 (Uniformly bounded nonzero coboundary representatives).** Define
$$
d'_m=\begin{cases}
1-t^m,&t\ne\infty,\ |t|<1,\\
t^{-m}-1,&t\ne\infty,\ |t|>1,\\
-1,&t=\infty.
\end{cases}
$$
For every positive $m,n$,
$$
1-\rho_t\le|d'_m|\le1+\rho_t,\qquad
c_{m,n}=\frac{d'_m d'_n}{d'_{m+n}}.
$$
In particular every $d'_m$ is nonzero, and the finite vectors
$$
u_m=\frac{v_m}{d'_m}
$$
satisfy
$$
u_m*_t u_n=u_{m+n}.
$$

**Proof.** For finite $t$ with $|t|<1$, the identity is the direct calculation
$$
\frac{(1-t^m)(1-t^n)}{1-t^{m+n}}
=-\frac{(t^m-1)(t^n-1)}{t^{m+n}-1}
=c_{m,n}.
$$
For $|t|>1$, write
$$
d'_m=t^{-m}(1-t^m).
$$
The factors $t^{-m}$ form a multiplicative character of the positive-index additive semigroup, so they cancel in the quotient:
$$
\frac{d'_m d'_n}{d'_{m+n}}
=\frac{t^{-m}t^{-n}}{t^{-(m+n)}}
\frac{(1-t^m)(1-t^n)}{1-t^{m+n}}
=c_{m,n}.
$$
This calculation is valid for negative $t$ as well; no positivity of the character is needed. For the formal parameter, the quotient is $(-1)(-1)/(-1)=-1=c_{m,n}$.

In each finite case, $|d'_m|$ has the form $|1-s^m|$ with $|s|=\rho_t<1$. Hence
$$
1-\rho_t\le1-\rho_t^m\le|1-s^m|\le1+\rho_t^m\le1+\rho_t.
$$
This proves the bounds for every index and sign. For $\infty$, both bounds are one. Therefore division by $d'_m$ is legitimate, and
$$
u_m*_t u_n
=\frac{c_{m,n}}{d'_m d'_n}v_{m+n}
=\frac{v_{m+n}}{d'_{m+n}}
=u_{m+n}.
$$
In particular $d'_m=1$ at $t=0$, whereas $d'_m=-1$ at the formal parameter; neither case requires a limiting argument. QED.

**theorem 27.7 (Explicit bounded coordinate isomorphism).** For $a\in B$, write
$$
a_m^+=a(x_m^+),\qquad a_m^-=a(x_m^-).
$$
Define $\Phi_t(a)=(f,g)$ by
$$
f(\theta)=\begin{cases}
a(k_\theta),&\theta\notin E,\\
a_m^++a_m^-,&\theta=E_m,
\end{cases}
$$
$$
g_m=d'_m\bigl((1-p_m)a_m^+-p_m a_m^-\bigr).
$$
The second coordinate can equivalently be written without $p_m$ as
$$
g_m=\begin{cases}
a_m^++t^m a_m^-,&t\ne\infty,\ |t|<1,\\
t^{-m}a_m^++a_m^-,&t\ne\infty,\ |t|>1,\\
a_m^-,&t=\infty.
\end{cases}
$$
Then $\Phi_t$ is a bounded algebra isomorphism from $B_t$ to $\mathcal B$. Its inverse $\Psi_t$ is given by
$$
\Psi_t(f,g)(k_\theta)=f(\theta)\qquad(\theta\notin E),
$$
$$
\Psi_t(f,g)(x_m^+)=p_m f(E_m)+\frac{g_m}{d'_m},\qquad
\Psi_t(f,g)(x_m^-)=(1-p_m)f(E_m)-\frac{g_m}{d'_m}.
$$
In the original coefficient norm, these maps satisfy
$$
\|\Phi_t(a)\|_{\oplus}\le2\|a\|_1,
$$
$$
\|\Psi_t(f,g)\|_1
\le C_t\|f\|_1+\frac{2}{1-\rho_t}\|g\|_1
\le\frac{2}{1-\rho_t}\|(f,g)\|_{\oplus}.
$$
In particular,
$$
\frac{1-\rho_t}{2}\|a\|_1\le\|\Phi_t(a)\|_{\oplus}\le2\|a\|_1.
$$
Under this isomorphism, the phase map is the first-coordinate projection and the augmentation is the sum of the first coordinate. All parameters yield isomorphic Banach algebras, but distinct parameters still yield distinct kernels on the fixed oriented point masses.

**Proof.** The simplifications of $g_m$ follow from explicit identities. When $|t|<1$,
$$
p_m=-\frac{t^m}{d'_m},\qquad 1-p_m=\frac1{d'_m}.
$$
When $|t|>1$,
$$
p_m=-\frac1{d'_m},\qquad 1-p_m=\frac{t^{-m}}{d'_m}.
$$
For $\infty$, one has $p_m=1$ and $d'_m=-1$. Substitution gives each displayed formula for $g_m$.

The coordinates of $f$ are precisely the fiber sums $H_{\#}a$, so $\|f\|_1\le\|a\|_1$. In the two finite cases the additional coefficient in the formula for $g_m$ has absolute value at most one. Consequently, including the formal case,
$$
\sum_{m\ge1}|g_m|\le\sum_{m\ge1}(|a_m^+|+|a_m^-|)\le\|a\|_1.
$$
This proves that $\Phi_t$ is a well-defined bounded linear map on the actual space of all absolutely summable families, and proves its stated upper bound.

Conversely, the formulas for $\Psi_t$ specify every coordinate of $K$, because the fibers in Assumption 25.1 exhaust $K$. Theorem 27.2 and theorem 27.6 imply
$$
\begin{aligned}
\|\Psi_t(f,g)\|_1
&\le\sum_{\theta\notin E}|f(\theta)|
+\sum_{m\ge1}(|p_m|+|1-p_m|)|f(E_m)|
+2\sum_{m\ge1}\frac{|g_m|}{|d'_m|}\\
&\le C_t\|f\|_1+\frac{2}{1-\rho_t}\|g\|_1.
\end{aligned}
$$
Thus the inverse formulas also give an actual absolutely summable family. Since $C_t=(1+\rho_t)/(1-\rho_t)\le2/(1-\rho_t)$, the final inverse bound follows.

The inverse identities can be checked coordinate by coordinate without any infinite basis assertion. Starting with $a$, one has
$$
\frac{g_m}{d'_m}
=(1-p_m)a_m^+-p_m a_m^-
=a_m^+-p_m f(E_m).
$$
Substitution into the formulas for $\Psi_t$ recovers both $a_m^+$ and $a_m^-$. Nonexceptional coordinates are unchanged. Starting instead with $(f,g)$, the two reconstructed exceptional coefficients sum to $f(E_m)$, and
$$
(1-p_m)\left(p_m f(E_m)+\frac{g_m}{d'_m}\right)
-p_m\left((1-p_m)f(E_m)-\frac{g_m}{d'_m}\right)
=\frac{g_m}{d'_m}.
$$
Hence the second coordinate is also recovered. Therefore $\Psi_t\Phi_t$ and $\Phi_t\Psi_t$ are the respective identity maps on their full absolutely summable spaces. The norm-equivalence inequality follows by applying the inverse bound to $\Phi_t(a)$.

It remains to prove multiplicativity. On the finite core, theorem 25.5 and nonzero rescaling give an algebraic basis consisting of the $\pi_\theta$ and $u_m$. The coordinate formulas give
$$
\Phi_t(\pi_\theta)=(\delta_\theta,0),\qquad
\Phi_t(u_m)=(0,\delta_m).
$$
The finite products of these vectors are
$$
\pi_\theta*_t\pi_\eta=\pi_{\theta+\eta},\qquad
\pi_\theta*_t u_m=u_m*_t\pi_\theta=0,\qquad
u_m*_t u_n=u_{m+n}.
$$
The last identity is theorem 27.6, and the others are the finite rules from Section 25. They agree exactly with the products of the corresponding coordinate vectors in $\mathcal B$. Thus $\Phi_t$ is multiplicative on the finite core. The finite core is dense, both products are bounded by theorem 27.5, and $\Phi_t$ is bounded. Taking finite-support limits proves multiplicativity on $B$. Its bounded inverse is consequently multiplicative as well. The estimates remain bounded estimates when the domain uses the equivalent norm $\|\cdot\|_{\mathrm{alg},t}$, establishing the claimed Banach-algebra isomorphism.

The formula for $f$ gives $f=H_{\#}a$. Absolute summability permits regrouping by fibers and gives
$$
\varepsilon(a)=\sum_{\theta\in\mathbb T}f(\theta).
$$
The two inverse images
$$
V_t=\Phi_t^{-1}(\mathcal G\oplus\{0\}),\qquad
J_t=\Phi_t^{-1}(\{0\}\oplus\mathcal S)
$$
are closed two-sided ideals, their cross products vanish, and $J_t=\ker H_{\#}$. Moreover,
$$
\Phi_t(\delta_{0_K})=(\delta_0,0),
$$
so $\delta_{0_K}$ is the unit of $V_t$ and annihilates $J_t$.

For any two parameters, composing one coordinate isomorphism with the inverse of the other gives an abstract Banach-algebra isomorphism. This does not identify the kernels on the fixed point-mass carrier. Indeed, their actual zero-slice coefficient is
$$
P^{(t)}_{0_K,x_1^+}(x_1^+)=\begin{cases}
\dfrac{t}{t-1},&t\ne\infty,\\
1,&t=\infty.
\end{cases}
$$
A finite parameter never gives the value one, and equality of the finite values implies equality of the parameters by cross multiplication. Thus distinct parameters give distinct kernels, even though the completed algebras are isomorphic. QED.

**theorem 27.8 (Absence of every one-sided approximate identity).** The algebra $B_t$ has no left approximate identity and no right approximate identity in its norm topology, even when unbounded nets are allowed. Hence it has no two-sided approximate identity and no left or right unit.

**Proof.** In $\mathcal B$, let $z=(0,\delta_1)$. For any $(f,g)\in\mathcal B$, the second coordinate of
$$
(f,g)\diamond z
$$
has first coefficient zero: positive integers cannot sum to one. The second coordinate of $z$ has first coefficient one. Therefore
$$
\|(f,g)\diamond z-z\|_{\oplus}\ge1.
$$
The identical argument gives
$$
\|z\diamond(f,g)-z\|_{\oplus}\ge1.
$$
Since $\Phi_t(u_1)=z$, the forward bound in theorem 27.7 yields, for every $a\in B$,
$$
\|a*_t u_1-u_1\|_1\ge\frac12,\qquad
\|u_1*_t a-u_1\|_1\ge\frac12.
$$
No net can therefore approximate the identity on even this one element, on either side. The coefficient norm and the Banach-algebra norm induce the same topology. A one-sided unit would provide a constant one-sided approximate identity, so units are excluded as well. The element $(\delta_0,0)$ is nevertheless a unit on the first summand alone; it annihilates $z$ and is not a unit of the direct sum. QED.

**definition 27.9 (Measure topologies).** Give $K$ its original digit topology, metrized by
$$
d_K(x,y)=\sum_{j\ge0}2^{-j-1}|x_j-y_j|.
$$
Let $C(K)$ denote the real continuous functions with the supremum norm, and let $M(K)$ denote the finite signed regular Borel measures with norm
$$
\|\mu\|_{\mathrm{TV}}=|\mu|(K).
$$
The measure weak topology used here is
$$
\sigma(M(K),C(K)),
$$
namely the topology generated by the maps
$$
\mu\longmapsto\int_K f\,d\mu\qquad(f\in C(K)).
$$
On a compact space, continuous functions are bounded, so this agrees with weak convergence of signed measures tested against all bounded continuous functions. Under the Riesz representation identification $M(K)=C(K)^*$, it is exactly the weak-star topology on that dual.[^rro27-measures]

The Banach weak topology on the measure space is instead
$$
\sigma(M(K),M(K)^*),
$$
where $M(K)^*$ is the full norm-continuous dual of the total-variation Banach space. The norm topology is the topology of $\|\cdot\|_{\mathrm{TV}}$. These definitions distinguish the measure weak topology from the Banach weak topology.[^rro27-topology]

**theorem 27.10 (Compactness and the atomic isometric embedding).** The digit space $K$ is compact and metrizable by $d_K$. Every $a\in B$ defines a finite signed regular Borel measure
$$
\iota(a)(D)=\sum_{x\in D}a(x)\qquad(D\subseteq K\text{ Borel}),
$$
and this gives a linear isometric embedding
$$
\iota:B\longrightarrow M(K),\qquad
\|\iota(a)\|_{\mathrm{TV}}=\|a\|_1.
$$
In particular, all the kernels can be regarded as finite signed regular Borel measures. For distinct points,
$$
\|\delta_x-\delta_y\|_1
=\|\delta_x-\delta_y\|_{\mathrm{TV}}=2.
$$

**Proof.** Agreement of the first $N$ digits bounds $d_K$ by the tail sum $2^{-N}$, while $d_K(x,y)<2^{-N}$ forces agreement of the first $N$ digits. Thus the metric induces the digit topology. Given a sequence in $K$, successively choose subsequences constant in each digit and take a diagonal subsequence. It converges coordinatewise, hence in $d_K$. Its limit still has no adjacent ones, since each prohibited adjacent pair is determined by two coordinates. Therefore $K$ is sequentially compact, and hence compact as a metric space.

For $a\in B$, theorem 27.3 gives at most countable support. Absolute summability permits interchange over disjoint Borel sets, so the displayed formula for $\iota(a)$ is countably additive. Splitting the coefficients into their positive and negative parts shows that its variation is
$$
|\iota(a)|(D)=\sum_{x\in D}|a(x)|.
$$
For completeness, the positive and negative coefficient measures are concentrated on disjoint countable Borel sets, so they are mutually singular and form the Jordan decomposition. The asserted variation formula follows.

This variation measure is regular. Given a Borel set $D$ and $\epsilon>0$, choose a finite subset of $D\cap\operatorname{supp}(a)$ whose omitted mass inside $D$ is less than $\epsilon$; this subset is compact and proves inner regularity. For outer regularity, choose a finite $F\subseteq\operatorname{supp}(a)$ with total omitted mass less than $\epsilon$. The open set
$$
U=K\setminus(F\setminus D)
$$
contains $D$ and satisfies
$$
|\iota(a)|(U\setminus D)<\epsilon.
$$
Thus the variation, and consequently both Jordan parts, are regular. Taking $D=K$ in the variation formula proves the isometry. Linearity follows from absolute summability, and injectivity follows by evaluating singleton sets. Finally, for $x\ne y$, the two nonzero coefficients of $\delta_x-\delta_y$ have absolute value one, giving norm two. QED.

**theorem 27.11 (Exact continuity locus for the compact digit topology).** For each fixed parameter, the map
$$
K^2\longrightarrow M(K),\qquad (x,y)\longmapsto P^{(t)}_{x,y},
$$
with the digit topology on its domain and $\sigma(M(K),C(K))$ on its codomain, is continuous at $(x,y)$ if and only if $\Gamma(x,y)$ is a singleton. Equivalently, its continuity locus is exactly
$$
\{(x,y):H(x)+H(y)\notin E\}
\ \cup\ 
\{(x_m^s,x_n^s):m,n\ge1,\ s\in\{+1,-1\}\}.
$$
No parameter gives a jointly continuous map on all of $K^2$.

**Proof.** First suppose $\Gamma(x,y)=\{w\}$. Normalization and support inclusion imply
$$
P^{(t)}_{x,y}=\delta_w.
$$
Let $U$ be any open neighborhood of $w$. The set
$$
\Gamma\cap\bigl(K^2\times(K\setminus U)\bigr)
$$
is compact: $K^3$ is compact and $\Gamma$ is closed. Its projection to $K^2$ is compact, hence closed, and does not contain $(x,y)$. Its complement therefore supplies a neighborhood $W$ of $(x,y)$ such that
$$
\Gamma(x',y')\subseteq U\qquad((x',y')\in W).
$$

Fix $f\in C(K)$ and $\epsilon>0$. Choose $U$ small enough that
$$
|f(z)-f(w)|<\frac{\epsilon}{C_t}\qquad(z\in U).
$$
For the corresponding neighborhood $W$, normalization of every row and theorem 27.2 give
$$
\begin{aligned}
\left|\int_K f\,dP^{(t)}_{x',y'}-f(w)\right|
&=\left|\int_K(f-f(w))\,dP^{(t)}_{x',y'}\right|\\
&\le\int_K|f-f(w)|\,d|P^{(t)}_{x',y'}|\\
&\le\|P^{(t)}_{x',y'}\|_{\mathrm{TV}}\,\frac{\epsilon}{C_t}
\le\epsilon.
\end{aligned}
$$
One may shrink $U$ further to make the last bound strict. Thus every continuous test integral is continuous at $(x,y)$, which is precisely continuity into $\sigma(M(K),C(K))$. This argument uses the uniform variation bound for signed rows; normalization alone would not control the absolute value of the integral.

Conversely, suppose $\Gamma(x,y)$ has two points. By Assumption 25.1 there is an index $r$ such that these points are
$$
w^+=x_r^+,\qquad w^-=x_r^-,\qquad w^+\ne w^-.
$$
Use the maximum product metric on $K^3$. For each sign $s$ and each integer $j\ge1$, membership of $(x,y,w^s)$ in the closure defining $\Gamma$ supplies actual natural numbers $a_j^s,b_j^s$ such that
$$
\max\left\{
 d_K(Z(a_j^s),x),\ d_K(Z(b_j^s),y),\ d_K(Z(a_j^s+b_j^s),w^s)
\right\}<\frac1j.
$$
For each sign this is one simultaneous approximation by a genuine input pair and its genuine finite sum, not a choice of unrelated input and output approximations. In particular,
$$
(Z(a_j^s),Z(b_j^s))\longrightarrow(x,y),\qquad
Z(a_j^s+b_j^s)\longrightarrow w^s.
$$
Finite-core consistency yields
$$
P^{(t)}_{Z(a_j^s),Z(b_j^s)}=\delta_{Z(a_j^s+b_j^s)}.
$$
For every $f\in C(K)$, its integral against the right side tends to $f(w^s)$. Thus these two sequences of output measures tend in the measure weak topology to $\delta_{w^+}$ and $\delta_{w^-}$, respectively. The continuity of point masses in this topology follows directly from evaluation on continuous functions.[^rro27-topology]

The two limits are distinct: some digit $q$ satisfies $w_q^+\ne w_q^-$, and the continuous function $f_q(z)=z_q$ separates the corresponding Dirac measures. Interleave the two actual input-pair sequences. The interleaved sequence still converges to $(x,y)$, whereas the integrals of its output measures against $f_q$ have two different subsequential limits. Hence the output map is not continuous at $(x,y)$. This conclusion applies even if the particular row $P^{(t)}_{x,y}$ itself is a Dirac measure.

It remains to identify the singleton locus. For a nonexceptional sum phase the exact graph formula in Assumption 25.1 gives a singleton. For an exceptional sum phase, the union of the two input sign sets is a singleton exactly when both inputs are exceptional and have the same sign. Their indices then add, producing precisely the second set in the displayed locus. Finally, $0_K$ is nonexceptional and
$$
\Gamma(0_K,x_1^+)=\{x_1^+,x_1^-\},
$$
so every parameter has at least this discontinuity. QED.

**theorem 27.12 (Separation from Banach weak and norm continuity).** For every parameter, the kernel map is measure-weak continuous at $(0_K,0_K)$ but is neither Banach-weak continuous nor total-variation-norm continuous there. The measure weak topology equals the weak-star topology specified in Definition 27.9, is strictly weaker than the Banach weak topology on $M(K)$, and the latter is strictly weaker than the total variation norm topology. Bounded bilinearity on $\ell^1(K_{\mathrm d})$ therefore does not imply digit-topology continuity of the point-mass kernel.

**Proof.** Let
$$
y_j=Z(G_j).
$$
This is the admissible digit word with its only nonzero digit at position $j$, so $y_j\to0_K$ in the digit topology and $y_j\ne0_K$. Finite-core consistency gives, independently of the parameter,
$$
P^{(t)}_{y_j,0_K}=\delta_{y_j},\qquad
P^{(t)}_{0_K,0_K}=\delta_{0_K}.
$$
For every $f\in C(K)$ one has $f(y_j)\to f(0_K)$, so the displayed outputs converge measure-weakly. Also $\Gamma(0_K,0_K)=\{0_K\}$ by Assumption 25.1, and theorem 27.11 proves continuity at that pair.

In contrast,
$$
\|\delta_{y_j}-\delta_{0_K}\|_{\mathrm{TV}}=2
$$
for every $j$, excluding norm continuity. The functional
$$
L:M(K)\to\mathbb R,\qquad L(\mu)=\mu(\{0_K\})
$$
is norm-continuous because $|L(\mu)|\le\|\mu\|_{\mathrm{TV}}$. It is consequently one of the tests defining the Banach weak topology. But
$$
L(\delta_{y_j})=0,\qquad L(\delta_{0_K})=1,
$$
so Banach weak continuity also fails. The same coordinate evaluation is a bounded functional on the coefficient space $B$.

Every continuous-function integral is norm-continuous on $M(K)$, so the measure weak topology is weaker than the Banach weak topology, which in turn is weaker than the norm topology. The preceding sequence makes the first inclusion strict. For strictness of the second, consider any basic Banach weak neighborhood of zero, defined by finitely many bounded linear functionals $L_1,\ldots,L_N$. The $N+1$ distinct point masses $\delta_{y_1},\ldots,\delta_{y_{N+1}}$ are linearly independent, as singleton evaluation verifies. The restriction of $(L_1,\ldots,L_N)$ to their span therefore has a nonzero kernel vector $\mu$. Every scalar multiple of $\mu$ satisfies all the defining zero-centered weak inequalities. Thus this weak neighborhood is unbounded in total variation, and no weak neighborhood of zero can be contained in a norm ball. The Banach weak and norm topologies are distinct.

Finally, the point-mass input map from digit $K$ to coefficient $B$ is not norm-continuous along $y_j\to0_K$, since its images stay at distance two. The bounded bilinear map in theorem 27.5 uses the coefficient norm on both input spaces, not the digit topology. There is therefore no implication from that bounded bilinearity to the digit-topology continuity excluded above. QED.

[^rro27-l1]: Adam Bobrowski and Wojciech Chojnacki, *Isolated points of spaces of homomorphisms from ordered AL-algebras*, Dissertationes Mathematicae, online-first text (2022), §3.1.3, pp. 21–22, especially equation (3.2), DOI 10.4064/dm845-11-2021. The cited section defines absolutely summable families over arbitrary sets and discrete semigroup convolution. [Mathematical text](https://cs.adelaide.edu.au/~wojtek/papers/dm845-11-2021.pdf).

[^rro27-ba]: Szymon Draga and Tomasz Kania, *When is multiplication in a Banach algebra open?*, arXiv:1704.08608v2, 7 October 2017, §§2.2–2.3. These sections specify the submultiplicative Banach-algebra norm convention and the convolution product for arbitrary discrete semigroups, for real or complex scalars. [Mathematical text](https://arxiv.org/html/1704.08608v2).

[^rro27-measures]: Martin Herdegen, Gechun Liang, and Osian Shelley, *Vague and weak convergence of signed measures*, arXiv:2205.13207v2 (2022), §1.1, Definition 1.1 and Theorem 1.2(a), pp. 2–3. These give the continuous-test definition of weak convergence for finite signed Radon measures and the Riesz representation identification with the continuous-function dual. [Mathematical text](https://arxiv.org/pdf/2205.13207v2).

[^rro27-topology]: Daniel V. Tausk, *Weak\** topology for the space of finite measures on a topological space*, notes dated 17 January 2024, Definition 3.1, p. 5; Proposition 4.1 and its proof, p. 8; Corollary C.6 and §C.1, p. 55. These distinguish the continuous-test topology from the Banach weak topology and establish continuity of the Dirac embedding in the former topology. [Mathematical text](https://www.ime.usp.br/~tausk/texts/WeakTopologyMeasures.pdf).

## 追加锚（本行以下为增补区）
## 28. All Radon measures, signed Borel convolution, and the boundary of uniqueness

**Assumption 28.0 (Fixed carrier and exact finite multiplication).** Retain Definition 25.0 and the exact-fiber and exact-graph hypotheses of Assumption 25.1. Give $K$ its original compact digit topology, and give $\mathbb T=\mathbb R/\mathbb Z$ its original compact group topology. Fix
$$
t\in(\mathbb R\setminus\{-1,1\})\sqcup\{\infty\},
$$
where $\infty$ is a separate formal parameter. Use the finite multiplication of Definition 25.8 and theorem 25.9. In particular, its rows $P^{(t)}_{x,y}$ are finite real signed measures, have mass one, are supported in the exact fiber $\Gamma(x,y)$, and satisfy
$$
P^{(t)}_{Z(a),Z(b)}=\delta_{Z(a+b)}.
$$
Write
$$
S=\{x_m^+,x_m^-:m\ge1\},\qquad K^\circ=K\setminus S,\qquad \mathbb T^\circ=\mathbb T\setminus E,
$$
$$
v_m=\delta_{x_m^+}-\delta_{x_m^-},\qquad
\pi_{E_m}=p_m\delta_{x_m^+}+(1-p_m)\delta_{x_m^-},\qquad
\pi_\theta=\delta_{k_\theta}\quad(\theta\notin E).
$$
The quantities $p_m,c_{m,n},\pi_\theta$ have the values belonging to this fixed parameter. All conclusions below are conditional on these exact carrier and graph hypotheses.

**definition 28.1 (Measure spaces and bounded residual coordinates).** For a compact metric space $X$, let $M(X)$ be the real vector space of all finite real signed regular Borel measures, with
$$
\|\mu\|_{\mathrm{TV}}=|\mu|(X),\qquad \varepsilon_X(\mu)=\mu(X).
$$
There is no factor of one half in this norm. A Borel map $f:X\to Y$ has pushforward
$$
(f_\#\mu)(D)=\mu(f^{-1}(D)).
$$
We use the classical compact Riesz representation identification $M(X)=C(X)^*$; in particular, $M(X)$ is complete. Its weak-star topology is $\sigma(M(X),C(X))$, not the Banach weak topology $\sigma(M(X),M(X)^*)$. These conventions are those of [Daniel V. Tausk, *Weak\* topology for the space of finite measures on a topological space*, §2, Definition 3.1, Corollary C.6 and §C.1](https://www.ime.usp.br/~tausk/texts/WeakTopologyMeasures.pdf).

Define
$$
\rho_t=\begin{cases}
|t|,&t\ne\infty,\ |t|<1,\\
|t|^{-1},&t\ne\infty,\ |t|>1,\\
0,&t=\infty,
\end{cases}
\qquad C_t=\frac{1+\rho_t}{1-\rho_t},
$$
$$
d'_m=\begin{cases}
1-t^m,&t\ne\infty,\ |t|<1,\\
t^{-m}-1,&t\ne\infty,\ |t|>1,\\
-1,&t=\infty.
\end{cases}
$$
For each positive integer $m$, define the Borel scalar function
$$
r_m(x)=d'_m\bigl((1-p_m)\mathbf1_{\{x_m^+\}}(x)-p_m\mathbf1_{\{x_m^-\}}(x)\bigr).
$$
Thus each $r_m$ is supported on its specified two-point fiber.

**theorem 28.2 (Uniform numerical bounds and actual maximizing rows).** For all positive integers $m,n$,
$$
1-\rho_t\le |d'_m|\le1+\rho_t,\qquad
c_{m,n}=\frac{d'_m d'_n}{d'_{m+n}}.
$$
The residual functions are explicitly
$$
r_m(x)=\begin{cases}
\mathbf1_{\{x_m^+\}}(x)+t^m\mathbf1_{\{x_m^-\}}(x),&|t|<1,\\
t^{-m}\mathbf1_{\{x_m^+\}}(x)+\mathbf1_{\{x_m^-\}}(x),&|t|>1,\\
\mathbf1_{\{x_m^-\}}(x),&t=\infty.
\end{cases}
$$
The finite-parameter cases in this display exclude the formal parameter. Consequently,
$$
\sum_{m\ge1}|r_m(x)|\le1\qquad(x\in K).
$$
Furthermore,
$$
\sup_{\theta\in\mathbb T}\|\pi_\theta\|_{\mathrm{TV}}\le C_t,
\qquad
\max_{x,y\in K}\|P^{(t)}_{x,y}\|_{\mathrm{TV}}=C_t.
$$
The maximum is attained at $(0_K,x_1^+)$ for finite $t\ge0$, at $(x_1^+,x_1^-)$ for finite $t<0$, and at $(0_K,0_K)$ for $t=\infty$.

**Proof.** If $|t|<1$, direct substitution gives
$$
d'_m(1-p_m)=1,\qquad -d'_mp_m=t^m.
$$
If $|t|>1$, it gives
$$
d'_m(1-p_m)=t^{-m},\qquad -d'_mp_m=1.
$$
For the formal parameter these two quantities are zero and one. This proves the formulas for $r_m$. Since the split fibers are pairwise disjoint and the displayed coefficients have absolute value at most one, the sum bound follows.

For $|t|<1$, the coboundary identity follows by substituting $d'_m=1-t^m$. For $|t|>1$, one has $d'_m=t^{-m}(1-t^m)$, and the character factors cancel in the quotient. For $\infty$, the quotient is $-1$. In both finite cases, $|d'_m|$ is of the form $|1-s^m|$ with $|s|=\rho_t<1$, so
$$
1-\rho_t\le1-\rho_t^m\le|1-s^m|\le1+\rho_t^m\le1+\rho_t.
$$
The formal case has absolute value one.

At a split phase, for finite $t$,
$$
\|\pi_{E_m}\|_{\mathrm{TV}}=\frac{1+|t|^m}{|1-t^m|}.
$$
For $|t|<1$, the reverse triangle inequality bounds this by $(1+\rho_t^m)/(1-\rho_t^m)\le C_t$. For $|t|>1$, divide numerator and denominator by $|t|^m$ and apply the same argument to $t^{-1}$. All other phase slices are Dirac measures. The formal parameter also gives only Dirac slices.

Rows with at least one non-split input are phase slices, and equal-sign split inputs give Dirac measures. For the remaining mixed row, theorem 25.9 gives
$$
M_{m,n}(t):=\|P^{(t)}_{x_m^+,x_n^-}\|_{\mathrm{TV}}
=\frac{|t|^n|t^m-1|+|t^n-1|}{|t^{m+n}-1|}.
$$
The other mixed type has norm $M_{n,m}(t)$. When $r=|t|<1$, triangle and reverse triangle inequalities give the sign-independent estimate
$$
M_{m,n}(t)
\le\frac{1+2r^n+r^{m+n}}{1-r^{m+n}}
\le\frac{1+2r+r^2}{1-r^2}
=\frac{1+r}{1-r}=C_t.
$$
This includes $t=0$. When $|t|>1$, multiplication by $|t|^{m+n}$ in the formula at $t^{-1}$ gives
$$
M_{m,n}(t)=M_{n,m}(t^{-1}),
$$
which reduces the estimate to the preceding case. Formal-parameter mixed rows are Dirac measures. This proves the bound for every row without a positivity assumption.

For finite $t\ge0$,
$$
\|P^{(t)}_{0_K,x_1^+}\|_{\mathrm{TV}}
=\frac{1+t}{|1-t|}=C_t.
$$
For finite $t<0$, the actual first mixed row simplifies to
$$
P^{(t)}_{x_1^+,x_1^-}
=\frac{t}{t+1}\delta_{x_2^+}+\frac1{t+1}\delta_{x_2^-},
$$
whose norm is $(1+|t|)/|t+1|=C_t$. The denominator is nonzero by the parameter restriction. Finally, $P^{(\infty)}_{0_K,0_K}=\delta_{0_K}$. These are actual input pairs, proving attainment. QED.

**theorem 28.3 (The inverse away from the split phases is a homeomorphism).** The restricted map
$$
H|_{K^\circ}:K^\circ\longrightarrow\mathbb T^\circ
$$
is a homeomorphism for the subspace topologies, and hence a Borel isomorphism. In particular,
$$
s(\theta)=\begin{cases}
k_\theta,&\theta\notin E,\\
x_m^-,&\theta=E_m
\end{cases}
$$
defines a Borel section $s:\mathbb T\to K$ with $H\circ s=\operatorname{id}_{\mathbb T}$.

**Proof.** The no-adjacent-ones condition defines a closed subset of the compact product $\{0,1\}^{\mathbb N}$, so $K$ is compact and metrizable. The series defining $F$ converges uniformly, because the absolute values of its terms are bounded by a summable geometric sequence. Each partial sum is continuous. Thus $F$, and consequently $H$, is continuous.

The exact-fiber assumption makes the restriction a continuous bijection. To prove continuity of its inverse, fix $\theta\in\mathbb T^\circ$ and an open neighborhood $U\subseteq K$ of $k_\theta$. The set $H(K\setminus U)$ is compact and therefore closed in $\mathbb T$. It does not contain $\theta$, since $H^{-1}(\{\theta\})=\{k_\theta\}$. Hence
$$
W=\mathbb T\setminus H(K\setminus U)
$$
is an open neighborhood of $\theta$, and $k_\eta\in U$ for every $\eta\in W\cap\mathbb T^\circ$. This proves the inverse continuity; it does not require $K^\circ$ to be compact.

Both $E$ and $S$ are countable Borel sets. For a Borel set $D\subseteq K$, the inverse image of $D$ under $s$ is the union of the Borel subset of $\mathbb T^\circ$ obtained from the inverse homeomorphism and a subset of the countable set $E$. It is therefore Borel in $\mathbb T$. The section identity follows from the fiber definitions. Choosing the other branch at any subset of the split phases also gives a Borel section, although the displayed choice will remain fixed. QED.

**theorem 28.4 (Setwise integration of uniformly bounded signed kernels).** Let $X,Y$ be compact metric spaces. Suppose that $Q_y\in M(X)$ for every $y\in Y$, that
$$
y\longmapsto Q_y(D),\qquad y\longmapsto |Q_y|(D)
$$
are Borel for every Borel $D\subseteq X$, and that $\sup_y\|Q_y\|_{\mathrm{TV}}\le B<\infty$. For $\eta\in M(Y)$ define
$$
I_Q\eta(D)=\int_Y Q_y(D)\,d\eta(y).
$$
Then $I_Q\eta$ is a finite signed regular Borel measure, depends linearly on $\eta$, and satisfies
$$
|I_Q\eta|(D)\le\int_Y|Q_y|(D)\,d|\eta|(y),\qquad
\|I_Q\eta\|_{\mathrm{TV}}\le B\|\eta\|_{\mathrm{TV}}.
$$
For every bounded real Borel function $f$ on $X$, the function
$$
Qf(y)=\int_X f\,dQ_y
$$
is Borel and bounded, and
$$
\int_X f\,d(I_Q\eta)=\int_Y Qf\,d\eta.
$$
All these integrals are scalar signed-measure integrals.

For finite signed measures $\mu\in M(X)$ and $\eta\in M(Y)$, their signed product measure is intrinsic and satisfies
$$
|\mu\otimes\eta|=|\mu|\otimes|\eta|.
$$
Every bounded Borel function on $X\times Y$ satisfies signed Fubini, with either integration order. The same assertion holds for finitely many factors.

The setwise measurability and measurable Jordan-part conditions are the signed-kernel conditions appearing in [Riccardo Passeggeri, *On the extension and kernels of signed bimeasures and their role in stochastic integration*, Theorem 3.4(d)–(e′)](https://arxiv.org/html/2009.10657v2). The positive-measure Fubini theorem used below is [Stephan Tornier, *Haar Measures*, Theorem 1.11](https://arxiv.org/html/2006.10956v1).

**Proof.** Each defining integrand is bounded by $B$, so it is integrable against every finite signed $\eta$. If $D_j$ are pairwise disjoint Borel sets, then
$$
Q_y\Bigl(\bigcup_{j=1}^N D_j\Bigr)\longrightarrow
Q_y\Bigl(\bigcup_{j\ge1}D_j\Bigr),
$$
and all the expressions on the left have absolute value at most $B$. Dominated convergence against $|\eta|$ proves countable additivity of $I_Q\eta$.

The set function
$$
R(D)=\int_Y|Q_y|(D)\,d|\eta|(y)
$$
is a finite positive Borel measure by monotone convergence, with $R(X)\le B\|\eta\|_{\mathrm{TV}}$. For every finite Borel partition $D=\bigsqcup_i D_i$,
$$
\sum_i|I_Q\eta(D_i)|
\le\int_Y\sum_i|Q_y(D_i)|\,d|\eta|(y)
\le R(D).
$$
Taking the supremum over these partitions proves the variation domination and norm bound.

For completeness, every finite positive Borel measure on a compact metric space is regular. An open set is an increasing union of compact subsets, obtained from positive distance to its closed complement. The class of Borel sets admitting inner compact and outer open approximations is closed under complements. It is closed under countable unions: choose outer open approximations with summable errors; for inner approximation, first retain finitely many members of the union up to a small measure error and then take a finite union of their compact approximations. Thus this class contains the Borel sigma-algebra. Apply this argument to the positive and negative parts of $I_Q\eta$. This also shows why a merely Borel section in theorem 28.3 still produces regular measures here. The standard regularity statement is also [Tausk, Lemma 3.4 and Corollary 3.5](https://www.ime.usp.br/~tausk/texts/WeakTopologyMeasures.pdf).

For a simple Borel function $f$, measurability of $Qf$ and the integration identity follow by finite linearity. Every bounded real Borel function has uniformly convergent simple approximations $f_j$. Since
$$
|Q(f_j-f)(y)|\le B\|f_j-f\|_\infty,
$$
the functions $Qf_j$ converge uniformly to $Qf$. Passing to the limit on both sides proves the assertion for every bounded Borel $f$. Linearity and independence of any representation of $\eta$ as a difference of positive measures follow from the intrinsic scalar signed integral.

For the product assertion, the four products of the Jordan parts define a finite signed measure whose value on a measurable rectangle is $\mu(A)\eta(B)$. Finite signed measures on the product sigma-algebra are determined by rectangles, by the pi-lambda theorem applied to their difference. Consequently any other positive-minus-positive decompositions produce the same measure, and this construction is bilinear.

Alternatively, write
$$
\mu=h_\mu|\mu|,\qquad \eta=h_\eta|\eta|,
$$
where the measurable signs have absolute value one almost everywhere with respect to the corresponding variation measures. The product measure has density $h_\mu(x)h_\eta(y)$ with respect to $|\mu|\otimes|\eta|$. This proves the variation identity. A bounded Borel function is absolutely integrable against that positive product, so positive-measure Fubini applied with these sign densities proves signed Fubini. Compact metric spaces have countable bases, hence their product Borel sigma-algebra is their Borel product sigma-algebra. Repeating the argument proves the finite-factor version. QED.

**theorem 28.5 (The Borel affine lift, including signed atom corrections).** For every Borel $D\subseteq K$, both
$$
\theta\longmapsto\pi_\theta(D),\qquad
\theta\longmapsto|\pi_\theta|(D)
$$
are Borel. The formulas
$$
L_t\nu(D)=\int_{\mathbb T}\pi_\theta(D)\,d\nu(\theta),\qquad \nu\in M(\mathbb T),
$$
define a bounded linear map $L_t:M(\mathbb T)\to M(K)$ satisfying
$$
\|L_t\nu\|_{\mathrm{TV}}\le C_t\|\nu\|_{\mathrm{TV}},\qquad
H_\#L_t\nu=\nu.
$$
With the section of theorem 28.3, there is the actual total-variation-convergent formula
$$
L_t\nu=s_\#\nu+\sum_{m\ge1}p_m\nu(\{E_m\})v_m.
$$
In particular,
$$
(L_t\nu)(\{x_m^+\})=p_m\nu(\{E_m\}),\qquad
(L_t\nu)(\{x_m^-\})=(1-p_m)\nu(\{E_m\}).
$$
No positivity of $p_m$ is required.

**Proof.** For every Borel $D$,
$$
\pi_\theta(D)=\mathbf1_D(s(\theta))
+\sum_{m\ge1}\mathbf1_{\{E_m\}}(\theta)p_m v_m(D).
$$
At each phase the sum has at most one nonzero term, so this is a Borel function. The variation evaluation is
$$
|\pi_\theta|(D)=\begin{cases}
\mathbf1_D(k_\theta),&\theta\notin E,\\
|p_m|\mathbf1_D(x_m^+)+|1-p_m|\mathbf1_D(x_m^-),&\theta=E_m.
\end{cases}
$$
It is Borel for the same reason. Theorem 28.2 and theorem 28.4 therefore construct $L_t$ with the asserted bound and regularity.

For any finite signed measure, finite partitions give
$$
\sum_{m\ge1}|\nu(\{E_m\})|\le\|\nu\|_{\mathrm{TV}}.
$$
Also $|p_m|\le C_t$ by theorem 28.2. Thus
$$
\sum_{m\ge1}\|p_m\nu(\{E_m\})v_m\|_{\mathrm{TV}}
\le2C_t\|\nu\|_{\mathrm{TV}}<\infty.
$$
The displayed correction series converges in $M(K)$. Absolute scalar domination permits integration of the preceding Borel formula term by term and proves that its sum is exactly $L_t\nu$. Since $s$ chooses the negative branch, evaluating the series on the two singleton sets gives the claimed atom formulas.

Finally, every $\pi_\theta$ has mass one and is supported on $H^{-1}(\{\theta\})$. Hence for every Borel $B\subseteq\mathbb T$,
$$
\pi_\theta(H^{-1}(B))=\mathbf1_B(\theta).
$$
Integrating proves $H_\#L_t\nu=\nu$. The construction uses setwise integration, not a total-variation Bochner integral. QED.

**definition 28.6 (The original-circle measure algebra and the residual algebra).** On $M(\mathbb T)$ use the ordinary signed measure convolution
$$
(\nu*_{\mathbb T}\xi)(B)
=\int_{\mathbb T}\int_{\mathbb T}\mathbf1_B(\theta+\eta)\,d\xi(\eta)\,d\nu(\theta).
$$
This is convolution of Borel measures on the original compact circle. It is not convolution on $\ell^1(\mathbb T_{\mathrm d})$. The usual measure-algebra convention is recalled in [Matthew Daws, *Characterising weakly almost periodic functionals on the measure algebra*, §2](https://arxiv.org/html/0904.0436v2).

Let
$$
\mathcal S=\ell^1(\mathbb N_{>0}),\qquad
\mathcal C=M(\mathbb T)\oplus_1\mathcal S,
$$
with standard sequence vectors $e_m$ and
$$
(g*_+h)_k=\sum_{\substack{m,n\ge1\\m+n=k}}g_mh_n,
$$
$$
(\nu,g)\diamond(\xi,h)=(\nu*_{\mathbb T}\xi,g*_+h),\qquad
\|(\nu,g)\|_\oplus=\|\nu\|_{\mathrm{TV}}+\|g\|_1.
$$
Cross products between the two summands are zero. In particular, $e_1*_+e_1=e_2$, and the first sequence coordinate of every residual product is zero.

**theorem 28.7 (The integrated point kernel on all measures, with its sharp norm).** For every Borel $D\subseteq K$, the maps
$$
(x,y)\longmapsto P^{(t)}_{x,y}(D),\qquad
(x,y)\longmapsto|P^{(t)}_{x,y}|(D)
$$
are Borel on $K^2$. The exact pointwise formula is
$$
P^{(t)}_{x,y}
=\pi_{H(x)+H(y)}
+\sum_{m,n\ge1}\frac{r_m(x)r_n(y)}{d'_{m+n}}v_{m+n}.
$$
At each input pair the sum has at most one nonzero term.

For all $\mu,\eta\in M(K)$, the formula
$$
(\mu\star_t\eta)(D)
=\int_K\int_K P^{(t)}_{x,y}(D)\,d\eta(y)\,d\mu(x)
$$
defines a bounded bilinear commutative operation on $M(K)$. Its outputs are finite signed regular Borel measures, and
$$
|\mu\star_t\eta|(D)
\le\int_{K^2}|P^{(t)}_{x,y}|(D)\,d(|\mu|\otimes|\eta|)(x,y),
$$
$$
\|\mu\star_t\eta\|_{\mathrm{TV}}
\le C_t\|\mu\|_{\mathrm{TV}}\|\eta\|_{\mathrm{TV}},\qquad
\|\star_t\|_{\mathrm{bil}}=C_t.
$$
It satisfies
$$
\varepsilon_K(\mu\star_t\eta)=\varepsilon_K(\mu)\varepsilon_K(\eta),
$$
$$
H_\#(\mu\star_t\eta)=(H_\#\mu)*_{\mathbb T}(H_\#\eta).
$$
It is the unique operation satisfying the displayed setwise kernel-integration law for every pair of measures and every Borel set. This assertion is not uniqueness from agreement on Dirac measures.

The operation takes every pair of positive measures to a positive measure exactly when $t\in\{0,\infty\}$.

**Proof.** The finite inverse basis formulas give, pointwise,
$$
\delta_x=\pi_{H(x)}+\sum_{m\ge1}\frac{r_m(x)}{d'_m}v_m,
$$
with at most one nonzero summand. Multiplying these two finite expressions, using the zero cross products and the coboundary identity of theorem 28.2, proves the displayed row formula.

The base term is Borel in every set evaluation by theorem 28.5 and continuity of addition and $H$. Every scalar summand in the correction is Borel, so the pointwise finite countable sum is Borel. In particular, ordinary nonexceptional output phases use their singleton measure, exceptional phases use the specified signed slice, and the remaining corrections occur only on the countable Borel set $S\times S$.

For variation measurability, outside $S\times S$ the row is exactly $\pi_{H(x)+H(y)}$, whose variation evaluations are Borel. On $S\times S$, its variation evaluation is obtained by replacing values at countably many Borel singleton input pairs by the variations of their actual finite rows. Such a replacement preserves Borel measurability. Thus both kernel hypotheses of theorem 28.4 hold, with bound $C_t$.

Apply that theorem to the signed product measure $\mu\otimes\eta$ on $K^2$. It gives countable additivity, variation domination, finite total variation and regularity. Signed Fubini gives both displayed iterated-integral interpretations. It also proves independence from choices of positive-minus-positive decompositions. Bilinearity follows from intrinsic signed integration and bilinearity of the signed product measure. The symmetry of the finite rows, followed by signed Fubini, gives commutativity.

The variation estimate proves the bilinear upper bound. Each attaining pair from theorem 28.2 consists of two norm-one Dirac measures, and their product is its actual row. Therefore the bilinear norm is exactly $C_t$.

Every row has mass one, so integration with $D=K$ proves the mass identity. Every row is supported in the phase fiber of $H(x)+H(y)$ and has mass one; consequently
$$
P^{(t)}_{x,y}(H^{-1}(B))=\mathbf1_B(H(x)+H(y)).
$$
Integrating, and using the pushforward integration formula in each variable, proves the phase-convolution identity for every Borel $B$. Equality on all Borel sets also proves uniqueness under the stated integration contract.

Finally, a real signed measure of mass one and total variation one is positive: its Jordan decomposition has negative mass zero. When $t\in\{0,\infty\}$, theorem 28.2 therefore makes every row positive, and integration against positive input measures preserves positivity. At every other parameter, $C_t>1$ and an attaining row has mass one but variation greater than one, so it is not positive. Its two positive Dirac inputs disprove positivity of the operation. QED.

**theorem 28.8 (The full phase kernel and the bounded coordinate isomorphism).** The phase pushforward has precisely the kernel
$$
\ker H_\#
=\left\{\sum_{m\ge1}b_mv_m:(b_m)_{m\ge1}\in\ell^1(\mathbb N_{>0})\right\}.
$$
Every such series converges in total variation, and
$$
\left\|\sum_{m\ge1}b_mv_m\right\|_{\mathrm{TV}}=2\sum_{m\ge1}|b_m|.
$$
For $\mu\in M(K)$, define
$$
R_t\mu=(g_m)_{m\ge1},\qquad
g_m=\int_K r_m\,d\mu
=d'_m\bigl((1-p_m)\mu(\{x_m^+\})-p_m\mu(\{x_m^-\})\bigr),
$$
$$
\Phi_t\mu=(H_\#\mu,R_t\mu).
$$
Then $\Phi_t:M(K)\to\mathcal C$ is a bounded linear bijection with inverse
$$
\Psi_t(\nu,g)=L_t\nu+\sum_{m\ge1}\frac{g_m}{d'_m}v_m.
$$
The bounds are
$$
\|\Phi_t\mu\|_\oplus\le2\|\mu\|_{\mathrm{TV}},
$$
$$
\|\Psi_t(\nu,g)\|_{\mathrm{TV}}
\le C_t\|\nu\|_{\mathrm{TV}}+\frac{2}{1-\rho_t}\|g\|_1
\le\frac{2}{1-\rho_t}\|(\nu,g)\|_\oplus.
$$
In particular,
$$
\frac{1-\rho_t}{2}\|\mu\|_{\mathrm{TV}}
\le\|\Phi_t\mu\|_\oplus\le2\|\mu\|_{\mathrm{TV}}.
$$

**Proof.** Suppose first that $H_\#\mu=0$. If $D\subseteq K^\circ$ is Borel, theorem 28.3 implies that $H(D)$ is Borel in $\mathbb T^\circ$, hence in $\mathbb T$. Uniqueness of these fibers gives $H^{-1}(H(D))=D$, and therefore
$$
\mu(D)=(H_\#\mu)(H(D))=0.
$$
Thus the restriction of $\mu$ to $K^\circ$ is zero as a signed measure, and $\mu$ is concentrated on $S$. On each split fiber,
$$
\mu(\{x_m^+\})+\mu(\{x_m^-\})=(H_\#\mu)(\{E_m\})=0.
$$
Set $b_m=\mu(\{x_m^+\})$. Countability of $S$ and finite variation now give
$$
\mu=\sum_{m\ge1}b_mv_m,\qquad 2\sum_{m\ge1}|b_m|=\|\mu\|_{\mathrm{TV}}.
$$
Conversely, every such absolutely convergent series has zero phase pushforward, since $H_\#v_m=0$ and pushforward is a contraction. This proves the kernel description using the Borel inverse, not density of atomic measures.

For arbitrary $\mu$, the simplified formulas in theorem 28.2 give
$$
\sum_{m\ge1}|g_m|
\le\sum_{m\ge1}\bigl(|\mu(\{x_m^+\})|+|\mu(\{x_m^-\})|\bigr)
=|\mu|(S)\le\|\mu\|_{\mathrm{TV}}.
$$
Also $\|H_\#\mu\|_{\mathrm{TV}}\le\|\mu\|_{\mathrm{TV}}$, by the variation inequality for pushforward, or directly by taking preimages of finite partitions. Thus $\Phi_t$ is well-defined and has the forward bound.

The lower bound on $|d'_m|$ proves absolute total-variation convergence of the inverse series and yields its stated estimate. On the phase lift, theorem 28.5 gives
$$
R_tL_t\nu=0.
$$
Indeed, each coordinate equals $d'_m((1-p_m)p_m-p_m(1-p_m))\nu(\{E_m\})=0$. Furthermore,
$$
H_\#(v_m/d'_m)=0,\qquad R_t(v_m/d'_m)=e_m.
$$
Boundedness of these maps permits passage through the absolutely convergent inverse series, proving $\Phi_t\Psi_t=\operatorname{id}_{\mathcal C}$.

For the other composition, put $\nu=H_\#\mu$. The measure $\mu-L_t\nu$ has zero phase pushforward and hence is a split-difference series by the first part of the proof. Its positive-branch coefficient is
$$
\mu(\{x_m^+\})-p_m\nu(\{E_m\})
=(1-p_m)\mu(\{x_m^+\})-p_m\mu(\{x_m^-\})
=\frac{g_m}{d'_m}.
$$
Thus $\Psi_t\Phi_t\mu=\mu$. Applying the inverse bound to $\Phi_t\mu$ proves the norm equivalence. QED.

**theorem 28.9 (Multiplicativity on all measures and associativity).** The coordinate bijection is an algebra isomorphism:
$$
\Phi_t(\mu\star_t\eta)=\Phi_t\mu\diamond\Phi_t\eta
\qquad(\mu,\eta\in M(K)).
$$
Consequently $\star_t$ is associative on all of $M(K)$, and
$$
(M(K),\star_t)\cong M(\mathbb T)\oplus\ell^1(\mathbb N_{>0})
$$
as real algebras with bounded maps in both directions. The norm
$$
N_t(\mu)=\|H_\#\mu\|_{\mathrm{TV}}+\|R_t\mu\|_1
$$
is complete, equivalent to total variation, and submultiplicative. The alternative norm $C_t\|\mu\|_{\mathrm{TV}}$ is also complete and submultiplicative. The unscaled total variation norm is submultiplicative exactly for $t\in\{0,\infty\}$.

Writing $g=R_t\mu$ and $h=R_t\eta$, the full product formula is
$$
\mu\star_t\eta
=L_t\bigl((H_\#\mu)*_{\mathbb T}(H_\#\eta)\bigr)
+\sum_{k\ge1}\frac{(g*_+h)_k}{d'_k}v_k.
$$
In particular, $L_tM(\mathbb T)$ and $\ker H_\#$ are closed ideals whose cross products vanish.

**Proof.** First, circle convolution is a contractive associative commutative product on $M(\mathbb T)$. Contractivity follows by pushforward under addition from
$$
|\nu\otimes\xi|=|\nu|\otimes|\xi|.
$$
For a bounded Borel test function and three input measures, both bracketings of circle convolution are the integral of $f(\theta+\eta+\zeta)$ against the same signed product measure. Its absolute integral is bounded by the product of the three variation norms times $\|f\|_\infty$. Theorem 28.4 therefore justifies all changes of integration order and proves associativity; symmetry proves commutativity. Absolute summation proves the analogous assertions and norm bound for $*_+$. Hence $\diamond$ is associative, commutative and submultiplicative for $\|\cdot\|_\oplus$, and $\mathcal C$ is complete.

The first coordinate of the desired multiplicativity is theorem 28.7. For a fixed positive integer $k$, the point-kernel formula and the identities used in theorem 28.8 give the exact scalar identity
$$
(R_tP^{(t)}_{x,y})_k
=\sum_{\substack{m,n\ge1\\m+n=k}}r_m(x)r_n(y).
$$
The left side is a fixed finite linear combination of two singleton evaluations of the output measure. Consequently the defining setwise integration law permits this coordinate to pass through the integral. The sum on the right is finite. Signed Fubini and the product-function identity now give
$$
\begin{aligned}
(R_t(\mu\star_t\eta))_k
&=\int_{K^2}(R_tP^{(t)}_{x,y})_k\,d(\mu\otimes\eta)(x,y)\\
&=\sum_{m+n=k}\left(\int_Kr_m\,d\mu\right)\left(\int_Kr_n\,d\eta\right)\\
&=(g*_+h)_k.
\end{aligned}
$$
This proves every residual coordinate for arbitrary signed measures, including non-atomic inputs. No approximation by atomic measures has been used.

Since $\Phi_t$ is injective and $\diamond$ is associative, both bracketings of any triple product in $M(K)$ have the same image under $\Phi_t$ and are equal. Applying $\Psi_t$ to the coordinate product proves the full product formula. Its series converges absolutely because
$$
\sum_{k\ge1}\left\|\frac{(g*_+h)_k}{d'_k}v_k\right\|_{\mathrm{TV}}
\le\frac{2}{1-\rho_t}\|g*_+h\|_1
\le\frac{2}{1-\rho_t}\|g\|_1\|h\|_1.
$$
The norm $N_t$ is the pullback of the complete submultiplicative direct-sum norm. Its equivalence to total variation is theorem 28.8. The sharp bilinear bound gives
$$
C_t\|\mu\star_t\eta\|_{\mathrm{TV}}
\le(C_t\|\mu\|_{\mathrm{TV}})(C_t\|\eta\|_{\mathrm{TV}}).
$$
When $C_t>1$, an attaining pair of unit-norm Dirac measures disproves submultiplicativity of the unscaled norm. When $C_t=1$, that norm is submultiplicative by theorem 28.7. Finally, the two coordinate summands are closed ideals with zero cross products, and their inverse images are exactly the two asserted ideals. QED.

**theorem 28.10 (Atomic and non-atomic signed parts are linear projections).** Let $X$ be a compact metric space. Every $\mu\in M(X)$ has a unique decomposition
$$
\mu=\mu_{\mathrm{at}}+\mu_{\mathrm{na}},\qquad
\mu_{\mathrm{at}}=\sum_{x\in X}\mu(\{x\})\delta_x,
$$
where the sum has at most countably many nonzero terms and converges in total variation, while $\mu_{\mathrm{na}}$ is non-atomic. Here non-atomic means that its variation measure has no atoms, not that it is absolutely continuous with respect to Haar measure. The two parts are mutually singular in variation and satisfy
$$
\|\mu\|_{\mathrm{TV}}=\|\mu_{\mathrm{at}}\|_{\mathrm{TV}}+\|\mu_{\mathrm{na}}\|_{\mathrm{TV}}.
$$
Both assignments are bounded linear projections of norm at most one. Their ranges $M_{\mathrm{at}}(X)$ and $M_{\mathrm{na}}(X)$ are closed.

On the circle, $M_{\mathrm{at}}(\mathbb T)$ is a convolution subalgebra, $M_{\mathrm{na}}(\mathbb T)$ is a convolution ideal, and
$$
(\nu*_{\mathbb T}\xi)_{\mathrm{at}}
=\nu_{\mathrm{at}}*_{\mathbb T}\xi_{\mathrm{at}}.
$$
In particular,
$$
a:M(\mathbb T)\to\mathbb R,\qquad a(\nu)=\nu_{\mathrm{na}}(\mathbb T)
$$
is a bounded linear functional with $|a(\nu)|\le\|\nu\|_{\mathrm{TV}}$, and vanishes on every atomic measure. It is not asserted to be multiplicative. This classical measure-algebra decomposition is recalled in [Daws, §3, the paragraph immediately preceding Lemma 3.7](https://arxiv.org/html/0904.0436v2).

**Proof.** For every positive integer $j$, there are only finitely many points with $|\mu(\{x\})|\ge1/j$, since any finite collection of them contributes its absolute masses to a variation bound. Thus
$$
A_\mu=\{x:\mu(\{x\})\ne0\}
$$
is countable and
$$
\sum_{x\in A_\mu}|\mu(\{x\})|\le\|\mu\|_{\mathrm{TV}}.
$$
The atomic series is therefore a measure in $M(X)$ and equals the restriction of $\mu$ to $A_\mu$. Its difference from $\mu$ is the restriction to $X\setminus A_\mu$. Since $|\mu|(\{x\})=|\mu(\{x\})|$, the latter restriction has zero variation on every singleton. The two restrictions are mutually singular, which proves the norm identity.

On a compact metric space, a finite positive Borel measure with no singleton atoms has no atoms at all. Indeed, construct refining finite Borel partitions whose mesh tends to zero. If a Borel set were an atom of positive mass, in each partition exactly one cell would contain its full mass. These cells can be selected nested. Continuity from above then gives full positive mass to their intersection with the atom, while the vanishing mesh makes that intersection contain at most one point. This would be a singleton atom. Apply this argument to the variation of the non-atomic restriction.

Linearity of the atomic part does not require the sets $A_\mu$ to be fixed as $\mu$ varies. For two measures, work on the countable union of their atomic sets. At every point, singleton evaluation is linear; the corresponding absolutely convergent atomic series is therefore linear as well. The non-atomic part is the difference from the identity and is consequently linear. The norm identity proves contractivity. Uniqueness follows because the non-atomic part has zero singleton masses and an atomic measure is determined by its singleton masses. The projection identities and closed ranges follow.

On $\mathbb T$, the convolution of two atomic measures is the absolutely convergent series of products of their atom coefficients at summed phases, so it remains atomic. If $\nu$ is non-atomic and $\xi$ is arbitrary, signed Fubini gives, for each $\theta$,
$$
(\nu*_{\mathbb T}\xi)(\{\theta\})
=\int_{\mathbb T}\nu(\{\theta-\eta\})\,d\xi(\eta)=0.
$$
Thus this convolution is non-atomic. Commutativity handles the other order. Expanding the two atomic/non-atomic decompositions proves the atomic-part convolution identity. Finally, $a$ is the composition of the non-atomic projection and the mass functional, both contractive linear maps. QED.

**theorem 28.11 (The Haar lift and the proper atomic completion).** Let $\lambda$ be normalized Haar measure on the original circle. Its existence as a regular probability measure follows from the classical Haar theorem; see [Tornier, Definition 2.1, Theorem 2.2 and Proposition 2.9](https://arxiv.org/html/2006.10956v1). Then
$$
\mathfrak m=L_t\lambda=s_\#\lambda
$$
is a non-atomic probability measure on $K$, independent of $t$ and independent of the branch choices at the split phases. It satisfies
$$
H_\#\mathfrak m=\lambda,\qquad R_t\mathfrak m=0,\qquad
\mathfrak m\star_t\mathfrak m=\mathfrak m.
$$
The atomic measures form a closed proper subalgebra
$$
M_{\mathrm{at}}(K)\cong\ell^1(K_{\mathrm d})\subsetneq M(K),
$$
with the isometric atomic embedding and the multiplication of Section 27. Under $\Phi_t$, this entire atomic subalgebra corresponds to
$$
\mathcal C_{\mathrm{at}}=M_{\mathrm{at}}(\mathbb T)\oplus\mathcal S.
$$
For every atomic signed measure $\alpha$ on $K$, the exact individual distance is
$$
\|\mathfrak m-\alpha\|_{\mathrm{TV}}=1+\|\alpha\|_{\mathrm{TV}}.
$$
Consequently,
$$
\operatorname{dist}_{\mathrm{TV}}(\mathfrak m,M_{\mathrm{at}}(K))=1.
$$
The distance to each atomic probability measure is two. Thus the distance one is a distance to the atomic signed subspace, not the distance to every member of that subspace.

**Proof.** Translation invariance makes all singleton Haar masses equal. For any positive integer $N$, selecting $N$ distinct points bounds this common mass by $1/N$, so it is zero. Hence $\lambda$ is non-atomic by theorem 28.10, and $\lambda(E)=0$. The atom-correction formula of theorem 28.5 reduces to $L_t\lambda=s_\#\lambda$. This is a probability measure. For $x\in K$,
$$
\mathfrak m(\{x\})=\lambda(s^{-1}(\{x\}))\le\lambda(\{H(x)\})=0,
$$
so it is non-atomic. Changing the section only on $E$ does not change its pushforward of $\lambda$, and the formula has no remaining parameter dependence.

The lift and residual identities have already been proved. Translation invariance also gives, for every Borel $B$,
$$
(\lambda*_{\mathbb T}\lambda)(B)
=\int_{\mathbb T}\lambda(B-\theta)\,d\lambda(\theta)=\lambda(B).
$$
The coordinate product then proves the idempotent identity for $\mathfrak m$.

Theorem 28.10 identifies atomic measures isometrically with absolutely summable point coefficients and proves their closedness. For atomic inputs, their signed product measure is itself an absolutely summable atomic measure on $K^2$. Thus the setwise integral in theorem 28.7 is the total-variation-convergent series
$$
\sum_{x,y}\mu(\{x\})\eta(\{y\})P^{(t)}_{x,y},
$$
whose sum of term norms is at most $C_t\|\mu\|_{\mathrm{TV}}\|\eta\|_{\mathrm{TV}}$. It remains atomic and is exactly the discrete convolution extension. If $\mu$ is atomic, its phase pushforward is atomic. Conversely, if $\nu$ is atomic, $L_t\nu$ is atomic by its defining slices and absolute convergence, and the residual inverse series is atomic. This proves the assertion about $\mathcal C_{\mathrm{at}}$.

For the distance formula, choose a countable Borel set supporting the variation of $\alpha$. The non-atomic measure $\mathfrak m$ assigns that set mass zero. Therefore $\mathfrak m$ and $|\alpha|$ are mutually singular and
$$
|\mathfrak m-\alpha|=\mathfrak m+|\alpha|.
$$
Taking total mass proves the individual formula; its infimum is one, attained at the zero atomic measure. Atomic probabilities have norm one, giving distance two.

Finite atomic measures are dense in $M_{\mathrm{at}}(K)$ by truncation of absolutely convergent series, and their closure in $M(K)$ is precisely this closed proper subspace. Hence the total-variation completion of the finite coefficient space is still $\ell^1(K_{\mathrm d})$. Passing to all of $M(K)$ enlarges the permitted measures; it is not that completion. The same conclusion holds for the equivalent norms in theorem 28.9. QED.

**theorem 28.12 (Setwise Borel measurability does not give norm-Borel measurability).** The maps
$$
x\longmapsto\delta_x\in M(K),\qquad
\theta\longmapsto\pi_\theta\in M(K)
$$
are not Borel maps when the target is given its total variation norm topology. Nevertheless, their Borel-set evaluations are Borel. Moreover, the map $\theta\mapsto\pi_\theta$ is not strongly measurable for normalized Haar measure in the total variation norm, and $L_t\lambda$ cannot be interpreted as its total-variation Bochner integral.

**Proof.** Distinct Dirac measures have total variation distance two. Also, for $\theta\ne\eta$, contraction of phase pushforward gives
$$
\|\pi_\theta-\pi_\eta\|_{\mathrm{TV}}
\ge\|\delta_\theta-\delta_\eta\|_{\mathrm{TV}}=2.
$$
For any subset $A\subseteq\mathbb T$, the norm-open set
$$
O_A=\bigcup_{\theta\in A}B_{\mathrm{TV}}(\pi_\theta,1)
$$
has inverse image exactly $A$ under the phase-slice map. The circle has non-Borel subsets, so this map cannot be norm-Borel. The same argument applies to the Dirac map on $K$. Indeed, $K$ has cardinality continuum because it maps onto the circle and is a subspace of $\{0,1\}^{\mathbb N}$; its Borel sigma-algebra has cardinality at most continuum, whereas its power set is larger. The scalar set evaluations were proved Borel in theorem 28.5, and are immediate for Dirac measures.

A strongly measurable Banach-valued function is, outside a null set, contained in the closure of the countable union of the ranges of its simple approximations, hence in a norm-separable set. A norm-separable set contains at most countably many members of a family whose distinct elements are separated by distance at least two. Thus strong measurability of $\theta\mapsto\pi_\theta$ would force a full Haar-measure set of phases to be countable. This contradicts non-atomicity of $\lambda$. Since Bochner integrability requires strong measurability, the proposed Bochner interpretation is impossible. The setwise construction of $L_t\lambda$ is unaffected. QED.

**theorem 28.13 (Explicit nonuniqueness despite agreement on the entire atomic algebra).** For each $\tau\in\mathbb R$, define
$$
U_\tau(\nu,g)=(\nu,g+\tau a(\nu)e_1)
\qquad((\nu,g)\in\mathcal C),
$$
where $a$ is the bounded linear functional of theorem 28.10. Then $U_\tau$ is a bounded linear isomorphism with inverse $U_{-\tau}$ and
$$
\|U_\tau\|\le1+|\tau|,\qquad \|U_\tau^{-1}\|\le1+|\tau|.
$$
Define the transported product
$$
z\diamond_\tau w
=U_\tau^{-1}\bigl(U_\tau z\diamond U_\tau w\bigr).
$$
This is a bounded associative commutative bilinear product. It agrees with $\diamond$ on the whole subalgebra $\mathcal C_{\mathrm{at}}$, has the same first-coordinate convolution, and preserves the first-coordinate mass character.

The corresponding products on $M(K)$,
$$
\mu\star_{t,\tau}\eta
=\Psi_t\bigl(\Phi_t\mu\diamond_\tau\Phi_t\eta\bigr),
$$
are bounded associative commutative extensions of the entire atomic algebra. They preserve mass and the usual phase convolution, and satisfy the same point rows
$$
\delta_x\star_{t,\tau}\delta_y=P^{(t)}_{x,y}
\qquad(x,y\in K).
$$
Nevertheless they are pairwise distinct as $\tau$ varies. For $z=(\lambda,0)$,
$$
z\diamond_\tau z=(\lambda,\tau^2e_2-\tau e_1),
$$
and therefore
$$
\mathfrak m\star_{t,\tau}\mathfrak m
=\mathfrak m-\frac{\tau}{d'_1}v_1+\frac{\tau^2}{d'_2}v_2.
$$
For every nonzero $\tau$, this product fails the setwise integration contract of theorem 28.7 and is not a positive operation.

**Proof.** Linearity of $a$ proves linearity of $U_\tau$. Since $U_\tau$ does not change the first coordinate, applying $U_{-\tau}$ subtracts exactly the same correction and proves the inverse formula. The bound follows from
$$
\|U_\tau(\nu,g)\|_\oplus
\le\|\nu\|_{\mathrm{TV}}+\|g\|_1+|\tau|\,|a(\nu)|
\le(1+|\tau|)\|(\nu,g)\|_\oplus.
$$
The inverse has the identical bound.

Transport through a linear isomorphism preserves bilinearity, associativity and commutativity. Explicitly, applying $U_\tau$ to either bracketing of a triple product gives the corresponding bracketing of $U_\tau z\diamond U_\tau w\diamond U_\tau u$. Also,
$$
\|z\diamond_\tau w\|_\oplus
\le(1+|\tau|)^3\|z\|_\oplus\|w\|_\oplus.
$$
Thus the transported product is bounded. Its complete submultiplicative norm can be taken to be $\|U_\tau z\|_\oplus$.

For $z=(\nu,g)$ and $w=(\xi,h)$, direct expansion gives
$$
\begin{aligned}
z\diamond_\tau w
=\bigl(\nu*_{\mathbb T}\xi,\;&g*_+h
+\tau a(\nu)(e_1*_+h)
+\tau a(\xi)(g*_+e_1)\\
&+\tau^2a(\nu)a(\xi)e_2
-\tau a(\nu*_{\mathbb T}\xi)e_1\bigr).
\end{aligned}
$$
Only linearity of $a$ is used; no multiplicativity assumption about it is needed. This formula proves directly that the first coordinate remains the ordinary circle convolution. Since its mass is the product of the two input masses, the mass character is preserved.

For every member of $\mathcal C_{\mathrm{at}}$, its first coordinate is atomic and hence has $a$ equal to zero. Thus $U_\tau$ is the identity on this whole subspace. The product of two such elements remains in $\mathcal C_{\mathrm{at}}$, because atomic circle measures form a convolution subalgebra. The inverse shear is therefore also the identity on their product, proving agreement on the full atomic subalgebra, not merely on finite sums or Dirac pairs.

The bounded coordinate isomorphisms transport these properties to $M(K)$. For example, an explicit sufficient total variation bound is
$$
\|\mu\star_{t,\tau}\eta\|_{\mathrm{TV}}
\le\frac{8(1+|\tau|)^3}{1-\rho_t}
\|\mu\|_{\mathrm{TV}}\|\eta\|_{\mathrm{TV}}.
$$
No sharpness is claimed for this estimate. Every Dirac measure belongs to the atomic subalgebra, giving the stated identical point rows.

Finally, $a(\lambda)=1$ and $\lambda*_{\mathbb T}\lambda=\lambda$. Hence
$$
U_\tau z=(\lambda,\tau e_1),\qquad
U_\tau z\diamond U_\tau z=(\lambda,\tau^2e_2).
$$
Applying the inverse shear gives the asserted Haar test. Its first residual coefficient is $-\tau$, so distinct real parameters give distinct products, including parameters with opposite signs.

The original setwise integral of the same rows against $\mathfrak m\otimes\mathfrak m$ is $\mathfrak m$, by theorem 28.11. In contrast, for $\tau\ne0$,
$$
(\mathfrak m\star_{t,\tau}\mathfrak m)(\{x_1^+\})=-\frac{\tau}{d'_1}\ne0,
$$
whereas $\mathfrak m(\{x_1^+\})=0$. Thus the sheared product fails that integration law on an actual Borel set. Moreover, the masses at $x_1^+$ and $x_1^-$ are nonzero opposites, because $\mathfrak m$ has no atoms and the second split fiber is disjoint from the first. One is negative. Therefore two positive input probabilities can have a nonpositive output. These sheared extensions are not probability-kernel integrations, even when their common point rows are probability measures. QED.

**theorem 28.14 (The global joint weak-star obstruction remains).** No globally jointly continuous product
$$
M(K)\times M(K)\longrightarrow M(K)
$$
for the topology $\sigma(M(K),C(K))$ on each measure space can agree with the prescribed point rows. In particular, neither the integrated product nor any sheared extension can have this global joint weak-star continuity. This concerns weak-star continuity, not total variation boundedness or the Banach weak topology.

**Proof.** The Dirac map from the original compact $K$ into $M(K)$ is weak-star continuous, because
$$
\int_K f\,d\delta_x=f(x)\qquad(f\in C(K)).
$$
This standard observation is [Tausk, Proposition 4.1 and its proof](https://www.ime.usp.br/~tausk/texts/WeakTopologyMeasures.pdf). A globally jointly weak-star continuous product agreeing on Diracs would therefore make
$$
(x,y)\longmapsto P^{(t)}_{x,y}
$$
continuous on $K^2$.

The exact graph hypothesis gives
$$
\Gamma(0_K,x_1^+)=\{x_1^+,x_1^-\}.
$$
For each sign $s\in\{+,-\}$, membership of $(0_K,x_1^+,x_1^s)$ in the closure defining $\Gamma$ supplies a sequence of genuine natural-number input pairs with
$$
Z(a_j^s)\longrightarrow0_K,\qquad
Z(b_j^s)\longrightarrow x_1^+,\qquad
Z(a_j^s+b_j^s)\longrightarrow x_1^s.
$$
These are simultaneous approximations of the input pair and its actual finite sum. Finite-core consistency gives
$$
P^{(t)}_{Z(a_j^s),Z(b_j^s)}=\delta_{Z(a_j^s+b_j^s)}.
$$
Consequently the two output sequences have weak-star limits $\delta_{x_1^+}$ and $\delta_{x_1^-}$. They are distinct: a digit coordinate at which the two points differ is a continuous function separating the limits. Interleaving the input sequences still gives convergence to $(0_K,x_1^+)$, but the corresponding continuous-test integrals have two different subsequential limits. The point-row map is therefore discontinuous there, independently of the parameter and independently of whether its value at that pair is itself a Dirac measure. This contradicts the proposed global joint continuity. QED.

## 追加锚（本行以下为增补区）
## 29. 原数字拓扑下的弱星拓扑中心与参数无关无原子理想

**定义 29.0（原载体、实测度与核记号）。** 沿用第25节的原数字载体及相位映射
$$
K=\{x\in\{0,1\}^{\mathbb N}:x_jx_{j+1}=0\text{ 对所有 }j\},\qquad d_K(x,y)=\sum_{j\ge0}2^{-j-1}|x_j-y_j|,
$$
$$
\phi=\frac{1+\sqrt5}{2},\qquad \alpha=\phi^{-1},\qquad H(x)=\left[\sum_{j\ge0}(-1)^{j+1}\alpha^{j+2}x_j\right]\in\mathbb T=\mathbb R/\mathbb Z.
$$
记
$$
E_m=[-m\phi],\qquad E=\{E_m:m\ge1\},\qquad S=H^{-1}(E),\qquad \mathcal O_+=\{[n\phi]:n\ge0\}.
$$
分裂纤维的定向点仍为 $x_m^+,x_m^-$，非分裂纤维的唯一点记为 $k_\theta$。记 $M(K)$ 为全部有限实有符号正则 Borel 测度，$C(K)$ 为实连续函数空间，并置
$$
\|\mu\|_{\mathrm{TV}}=|\mu|(K),\qquad \langle\mu,f\rangle=\int_K f\,d\mu,\qquad M_c(K)=\{\mu\in M(K):\mu(\{x\})=0\text{ 对每个 }x\in K\}.
$$
这里的无原子条件约束每个单点质量，不是仅要求总质量为零。圆周上的 $M(\mathbb T)$ 与 $M_c(\mathbb T)$ 同样定义。对 Borel 映射 $R$，推前定义为 $R_\#\mu(D)=\mu(R^{-1}(D))$。由 Riesz 表示定理，$M(K)=C(K)^*$，本文的弱星拓扑严格指
$$
\sigma(M(K),C(K)),
$$
而不是 $\sigma(M(K),M(K)^*)$ 或总变差范数拓扑。[^rro29-riesz]

取
$$
\Lambda=(\mathbb R\setminus\{-1,1\})\sqcup\{\infty\},\qquad P_t=P^{(t)},\qquad v_m=\delta_{x_m^+}-\delta_{x_m^-},
$$
其中 $P^{(t)}$ 是定义25.8的固定点核，$\infty$ 是独立的形式参数。$\pi_\theta,p_m,c_{m,n}$ 均使用该参数在第25节中的值。行界记为
$$
C_t=\frac{1+|t|}{\bigl|1-|t|\bigr|}\quad(t\ne\infty),\qquad C_\infty=1.
$$

**假设 29.1（精确几何与全测度逐集合积分契约）。** 采用假设25.1的精确相位纤维及精确闭图公式、假设26.1的任意提升严格单侧收敛，以及定理25.6—25.9的有限核恒等式和定理27.2的统一行界。特别，$K$ 紧致，$H$ 连续满射，
$$
H^{-1}(\{E_m\})=\{x_m^+,x_m^-\},\qquad H^{-1}(\{\theta\})=\{k_\theta\}\quad(\theta\notin E),\qquad H^{-1}(\{[n\phi]\})=\{Z(n)\}\quad(n\ge0).
$$
闭集 $\Gamma\subseteq K^3$ 是实际有限加法图的闭包，每行满足
$$
P_t(a,x)(K)=1,\qquad \operatorname{supp}P_t(a,x)\subseteq\Gamma(a,x)\subseteq H^{-1}(\{H(a)+H(x)\}),\qquad \|P_t(a,x)\|_{\mathrm{TV}}\le C_t.
$$
若 $\theta\notin E$，则相位 $\theta$ 的纤维为单点；若 $\epsilon_n>0$ 趋于零，且任意所选提升满足 $H(y_n)=E_j+[s\epsilon_n]$，其中 $s\in\{+1,-1\}$ 固定，则 $y_n\to x_j^s$。

对每个所讨论的参数 $t$，另假定给定有界双线性运算
$$
\star_t:M(K)\times M(K)\longrightarrow M(K),
$$
并满足以下逐集合契约：对每个 Borel 集 $D\subseteq K$，函数 $(a,x)\mapsto P_t(a,x)(D)$ 在 $K^2$ 上联合 Borel 可测，且
$$
(\mu\star_t\nu)(D)=\int_K\left(\int_K P_t(a,x)(D)\,d\mu(a)\right)d\nu(x).
$$
各行均为有限实有符号测度，且具有上述统一总变差界。本节关于全测度乘法的结论均以这一契约为前提。这里的有界有符号核及其积分算子采用通常的逐集合可测定义。[^rro29-kernel]

**定理 29.2（直接有符号积分恒等式与结合交换律）。** 对任意有界 Borel 实函数 $f$，定义
$$
P_{t,f}(a,x)=\int_K f(z)\,dP_t(a,x)(z).
$$
该函数联合 Borel 可测，并且
$$
|P_{t,f}(a,x)|\le C_t\|f\|_\infty,
$$
$$
\langle\mu\star_t\nu,f\rangle=\int_K\int_K P_{t,f}(a,x)\,d\mu(a)\,d\nu(x).
$$
这些积分可交换顺序。运算满足
$$
\|\mu\star_t\nu\|_{\mathrm{TV}}\le C_t\|\mu\|_{\mathrm{TV}}\|\nu\|_{\mathrm{TV}},\qquad (\mu\star_t\nu)(K)=\mu(K)\nu(K),
$$
且在全部 $M(K)$ 上结合、交换。

**证明。** 对简单 Borel 函数，$P_{t,f}$ 的可测性及测试积分公式直接来自逐集合契约和线性。任意有界 Borel 实函数均可由简单 Borel 函数一致逼近。行界给出
$$
\sup_{a,x}|P_{t,f}(a,x)-P_{t,g}(a,x)|\le C_t\|f-g\|_\infty,
$$
故一致极限仍可测，并给出所述界。测试积分公式的左边可用输出测度的有限总变差取一致极限，右边则由上述界取一致极限，因此公式对全部有界 Borel $f$ 成立。

对任意输入测度，实际绝对可积界为
$$
\int_K\int_K|P_{t,f}(a,x)|\,d|\mu|(a)\,d|\nu|(x)\le C_t\|f\|_\infty\|\mu\|_{\mathrm{TV}}\|\nu\|_{\mathrm{TV}}<\infty.
$$
将每个有符号输入写成其两个有限正 Jordan 部分，对所得四个正乘积测度应用 Fubini 定理，便可交换两个积分。此处使用联合 Borel 可测性、有限性及明确的绝对可积界，不仅使用两个迭代积分各自存在。相同的 Jordan 分解也把下文的有符号支配收敛化为对有限正变差测度的通常支配收敛。[^rro29-integration]

对 $\|f\|_\infty\le1$ 的连续函数取上确界，并使用 Riesz 等距表示，即得乘法范数估计。取 $f=1$，由每行质量为一得到质量恒等式。取两个点质量，逐集合契约给
$$
\delta_a\star_t\delta_x=P_t(a,x).
$$
因此第25节的每条有限线性组合恒等式，对这些有限测度同样成立。

第25节的点核交换律由其实际基乘法推出：相位基按圆周加法相乘，混合项为零，而 $c_{m,n}=c_{n,m}$。故 $P_t(a,x)=P_t(x,a)$。结合上面已经合法的有符号 Fubini，得到 $\mu\star_t\nu=\nu\star_t\mu$。

为证明全测度结合律，固定有界 Borel $f$，置
$$
A_f(a,b,c)=\int_K P_{t,f}(u,c)\,dP_t(a,b)(u),\qquad B_f(a,b,c)=\int_K P_{t,f}(a,v)\,dP_t(b,c)(v).
$$
有限点核的结合律给出每个有序三元组上的实际等式 $A_f(a,b,c)=B_f(a,b,c)$。二者均为 Borel 函数：带参数核积分的可测性先对函数 $\mathbf1_D(u)\mathbf1_F(c)$ 由逐集合可测性成立，再对有界单调极限使用每行有限变差的支配收敛；函数单调类定理遂覆盖全部有界联合 Borel 被积函数。并且
$$
|A_f(a,b,c)|,\ |B_f(a,b,c)|\le C_t^2\|f\|_\infty.
$$
两次应用已证的测试积分公式，并对有限 Jordan 部分应用 Fubini，得到
$$
\langle(\mu\star_t\nu)\star_t\omega,f\rangle=\iiint A_f(a,b,c)\,d\mu(a)\,d\nu(b)\,d\omega(c),
$$
$$
\langle\mu\star_t(\nu\star_t\omega),f\rangle=\iiint B_f(a,b,c)\,d\mu(a)\,d\nu(b)\,d\omega(c).
$$
每次展开的绝对积分不超过
$$
C_t^2\|f\|_\infty\|\mu\|_{\mathrm{TV}}\|\nu\|_{\mathrm{TV}}\|\omega\|_{\mathrm{TV}}.
$$
逐点等式 $A_f=B_f$ 因而给出两种括号的积分相等。对指标函数取值即得测度相等。这一证明直接积分点核恒等式，没有使用原子测度在全测度空间中的总变差稠密性。证毕。

**定义 29.3（指定乘法的弱星拓扑中心）。** 对 $\mu\in M(K)$，定义
$$
L_\mu^{(t)}\nu=\mu\star_t\nu,\qquad \mathcal T_\mu^{(t)}f(x)=\int_K P_{t,f}(a,x)\,d\mu(a).
$$
令
$$
Z_{\mathrm{top}}(\star_t)=\{\mu\in M(K):L_\mu^{(t)}\text{ 在全部 }M(K)\text{ 上弱星连续}\}.
$$
这里弱星连续是相对于定义29.0的同一个拓扑，在定义域和陪域上均取 $\sigma(M(K),C(K))$。该定义采用左乘算子的全域弱星连续性这一通常的拓扑中心含义；不预先假设整个乘法具有任何一侧的全域弱星连续性。[^rro29-center]

**定理 29.4（精确的前伴随判据）。** 对固定 $\mu$，以下条件等价：$\mu\in Z_{\mathrm{top}}(\star_t)$；对每个 $f\in C(K)$，实际有界 Borel 函数 $\mathcal T_\mu^{(t)}f$ 属于 $C(K)$。条件成立时，
$$
\mathcal T_\mu^{(t)}:C(K)\longrightarrow C(K)
$$
是有界线性算子，且
$$
\|\mathcal T_\mu^{(t)}\|\le C_t\|\mu\|_{\mathrm{TV}},\qquad L_\mu^{(t)}=(\mathcal T_\mu^{(t)})^*.
$$

**证明。** 对任意 $g\in C(K)$，$\langle\delta_x,g\rangle=g(x)$，故 $x\mapsto\delta_x$ 从 $K$ 到弱星测度空间连续。若 $L_\mu^{(t)}$ 弱星连续，则
$$
x\longmapsto\langle L_\mu^{(t)}\delta_x,f\rangle=\mathcal T_\mu^{(t)}f(x)
$$
是连续映射的复合，得到必要性。

反之，假定每个实际函数 $\mathcal T_\mu^{(t)}f$ 连续。积分线性及定理29.2的界表明它们组成所述有界线性算子。对任意 $\nu\in M(K)$，直接有符号积分给
$$
\langle L_\mu^{(t)}\nu,f\rangle=\int_K\mathcal T_\mu^{(t)}f(x)\,d\nu(x)=\langle\nu,\mathcal T_\mu^{(t)}f\rangle.
$$
因此它正是前伴随。若任意网 $\nu_i\to\nu$ 弱星收敛，对每个固定 $f\in C(K)$，右边按弱星收敛定义趋于 $\langle\nu,\mathcal T_\mu^{(t)}f\rangle$，所以 $L_\mu^{(t)}\nu_i\to L_\mu^{(t)}\nu$ 弱星收敛。这里不对输入网另加范数有界假设。判据约束全部连续测试在全部 $K$ 上的连续性，不是只检查若干输入处的点行连续性。证毕。

**定理 29.5（无原子测度的充分性）。** 对每个参数及每个 $\mu\in M_c(K)$，
$$
\mu\in Z_{\mathrm{top}}(\star_t),\qquad \|\mathcal T_\mu^{(t)}\|\le\|\mu\|_{\mathrm{TV}}.
$$

**证明。** 对实有符号测度，单点上的变差满足 $|\mu|(\{a\})=|\mu(\{a\})|$。因此无原子 $\mu$ 的变差对每个可数集合为零。

固定极限输入 $x$，考虑
$$
N_x=H^{-1}\bigl(E\cup(E-H(x))\bigr),\qquad E-H(x)=\{E_r-H(x):r\ge1\}.
$$
集合 $E$ 与 $E-H(x)$ 都可数，而每个 $H$ 纤维至多含两个点，所以 $N_x$ 可数，并且 $|\mu|(N_x)=0$。这同时涵盖固定分裂集与该输入所对应的平移分裂集。

设 $x_n\to x$，固定 $a\notin N_x$。此时 $H(a)+H(x)\notin E$，精确闭图给 $\Gamma(a,x)=\{w\}$。对任意 $w$ 的开邻域 $U$，最终有 $\Gamma(a,x_n)\subseteq U$。否则可取子列及 $w_n\in\Gamma(a,x_n)\setminus U$；由紧致性再取 $w_n$ 的收敛子列，闭图性使其极限属于 $\Gamma(a,x)$，同时属于闭集 $K\setminus U$，矛盾。

固定 $f\in C(K)$。利用行质量一、行支撑及统一总变差界，得到
$$
|P_{t,f}(a,x_n)-f(w)|\le C_t\sup_{z\in\Gamma(a,x_n)}|f(z)-f(w)|\longrightarrow0.
$$
且 $P_{t,f}(a,x)=f(w)$。所以被积函数对 $|\mu|$ 几乎处处收敛，差值由可积常数 $2C_t\|f\|_\infty$ 支配。对 $|\mu|$ 使用支配收敛，再用 Jordan 分解，得到
$$
\mathcal T_\mu^{(t)}f(x_n)\longrightarrow\mathcal T_\mu^{(t)}f(x).
$$
由于 $K$ 为度量空间，这证明实际函数连续。定理29.4给出弱星连续性。

对每个固定 $x$，在 $N_x$ 外的实际行是点质量，故还有
$$
|\mathcal T_\mu^{(t)}f(x)|\le\|f\|_\infty|\mu|(K).
$$
取上确界即得改进的算子范数界。证明只得到连续测试积分的收敛，并未把不同点质量误认为在总变差范数中相近。证毕。

**定理 29.6（Borel 截面与无原子相位提升）。** 对 $s\in\{+1,-1\}$，定义实际截面 $s_s:\mathbb T\to K$：当 $\theta\notin E$ 时，$s_s(\theta)=k_\theta$；当 $\theta=E_m$ 时，$s_s(\theta)=x_m^s$。这两个截面均为 Borel 映射，并满足 $H\circ s_s=\operatorname{id}_{\mathbb T}$。推前限制
$$
H_\#:M_c(K)\longrightarrow M_c(\mathbb T)
$$
是等距线性双射，其逆为任一 $(s_s)_\#$。特别，对 $\eta\in M_c(\mathbb T)$，两个截面给出同一个提升。

**证明。** 若 $F\subseteq K$ 闭，则 $H(F)$ 紧而闭，且
$$
s_s^{-1}(F)=\bigl(H(F)\setminus E\bigr)\cup\{E_m:x_m^s\in F\}.
$$
右边是 Borel 集，所以 $s_s$ 为 Borel 映射。截面恒等式由定义逐相位成立。

为说明这些 Borel 推前仍属于所指定的正则测度空间，先核对紧度量空间上有限 Borel 测度的正则性。对有限正 Borel 测度 $\xi$，闭集 $F$ 可由开集 $\{x:d(x,F)<1/n\}$ 从外逼近；由有限测度的向下连续性，外误差趋于零。开集 $U$ 可由闭集 $\{x:d(x,X\setminus U)\ge1/n\}$ 从内逼近；$U=X$ 时直接取 $X$。允许任意小紧内逼近及开外逼近误差的 Borel 集族对补集封闭。它也对可数并封闭：外逼近选可求和误差，内逼近先用有限性截取有限个集合使遗漏质量任意小，再取这些集合的有限个紧内逼近之并。该集族包含闭集，故包含全部 Borel 集。对有限有符号测度的两个 Jordan 部分分别应用，即得所需正则性。

任意 Borel 推前均满足
$$
\|R_\#\xi\|_{\mathrm{TV}}\le\|\xi\|_{\mathrm{TV}},
$$
因为任意有限 Borel 分割的原像仍是可测分割。若 $\eta\in M_c(\mathbb T)$，则 $s_s^{-1}(\{x\})$ 至多为单点，故 $(s_s)_\#\eta$ 无原子。反之，若 $\mu\in M_c(K)$，每个 $H$ 纤维至多为二点，故 $H_\#\mu$ 无原子。

截面恒等式给 $H_\#(s_s)_\#\eta=\eta$。另一方面，$s_s\circ H$ 与 $\operatorname{id}_K$ 只可能在可数集 $S$ 上不同，而 $|\mu|(S)=0$，所以对每个 Borel $D$，其两个原像的对称差为 $|\mu|$ 零集。因此
$$
(s_s)_\#H_\#\mu=\mu.
$$
这证明互逆关系及截面选择无关性。对互逆映射分别使用推前范数不增，便得
$$
\|H_\#\mu\|_{\mathrm{TV}}=\|\mu\|_{\mathrm{TV}},\qquad \|(s_s)_\#\eta\|_{\mathrm{TV}}=\|\eta\|_{\mathrm{TV}}.
$$
整个逆构造使用了实际 Borel 截面，而不是集合基数比较。证毕。

**定理 29.7（共同闭理想、通常圆周卷积与 Haar 提升）。** 在原圆周上，以
$$
(\eta*_{\mathbb T}\beta)(B)=\int_{\mathbb T}\int_{\mathbb T}\mathbf1_B(\lambda+\rho)\,d\eta(\lambda)\,d\beta(\rho)
$$
表示通常的有限有符号测度卷积。对任意 $\mu,\nu\in M(K)$，
$$
H_\#(\mu\star_t\nu)=(H_\#\mu)*_{\mathbb T}(H_\#\nu).
$$
若两个输入至少一个属于 $M_c(K)$，则对任一截面 $s_s$，都有更强的实际测度等式
$$
\mu\star_t\nu=(s_s)_\#\bigl((H_\#\mu)*_{\mathbb T}(H_\#\nu)\bigr)\in M_c(K),
$$
$$
\|\mu\star_t\nu\|_{\mathrm{TV}}\le\|\mu\|_{\mathrm{TV}}\|\nu\|_{\mathrm{TV}}.
$$
因此只要所比较的运算均满足假设29.1，这个乘积就与参数无关。$M_c(K)$ 是所有这些代数共同的非零、真、总变差闭双侧理想，且
$$
H_\#:(M_c(K),\star_t)\longrightarrow(M_c(\mathbb T),*_{\mathbb T})
$$
是等距实代数同构。通常测度代数中的连续测度理想采用的正是这种无单点原子的含义。[^rro29-ideal]

此外，若 $\mu\in M_c(K)$、$f\in C(K)$，则
$$
\mathcal T_\mu^{(t)}f=g_{\mu,f}\circ H,\qquad g_{\mu,f}(\theta)=\int_{\mathbb T}f(s_s(\lambda+\theta))\,d(H_\#\mu)(\lambda),\qquad g_{\mu,f}\in C(\mathbb T).
$$
令 $m_{\mathbb T}$ 为圆周上的归一化 Haar 测度，定义
$$
\lambda_K=(s_s)_\#m_{\mathbb T}.
$$
该定义与符号选择无关，且对每个 $\mu\in M(K)$，
$$
\lambda_K\star_t\mu=\mu\star_t\lambda_K=\mu(K)\lambda_K.
$$

**证明。** 圆周加法连续，因此上述通常卷积是有限有符号乘积测度在加法映射下的推前；有限 Jordan 分解及定理29.6证明中的正则性论证保证它是有限正则测度。其总变差不超过 $\|\eta\|_{\mathrm{TV}}\|\beta\|_{\mathrm{TV}}$。

对 Borel $B\subseteq\mathbb T$，点核的相位支撑及行质量给
$$
P_t(a,x)(H^{-1}(B))=\mathbf1_B(H(a)+H(x)).
$$
直接代入逐集合积分契约，再用推前的积分公式，即得对任意两个全测度成立的相位乘法恒等式。

现设 $\mu\in M_c(K)$。固定第二输入 $x$，除去定理29.5中的可数集 $N_x$ 后，和相位非分裂，故实际行准确等于
$$
P_t(a,x)=\delta_{s_s(H(a)+H(x))}.
$$
两个逐集合被积函数在 $N_x$ 上可能不同，但该集对 $|\mu|$ 为零。所以对每个 Borel $D\subseteq K$，
$$
\int_K P_t(a,x)(D)\,d\mu(a)=\int_K\mathbf1_D(s_s(H(a)+H(x)))\,d\mu(a).
$$
右边的联合被积函数是 Borel 且有界。对 $x$ 积分，并应用有限有符号 Fubini 及两次推前公式，得到所述提升公式。

若 $\eta\in M_c(\mathbb T)$、$\beta\in M(\mathbb T)$，则对每个 $\theta\in\mathbb T$，直接有符号积分给
$$
(\eta*_{\mathbb T}\beta)(\{\theta\})=\int_{\mathbb T}\eta(\{\theta-\rho\})\,d\beta(\rho)=0.
$$
因此圆周卷积无原子。定理29.6表明其提升也无原子，并且两个截面产生同一个实际测度。所得公式不含参数，给出参数独立性。范数不等式由圆周卷积范数界及提升等距性得到。若第二输入无原子，则利用定理29.2已经由积分证明的交换律，得到同样结论。

每个单点评价 $\mu\mapsto\mu(\{x\})$ 都是总变差有界线性泛函，所以
$$
M_c(K)=\bigcap_{x\in K}\ker\bigl(\mu\mapsto\mu(\{x\})\bigr)
$$
是闭线性子空间。刚证明的乘积性质使其成为双侧理想。定理29.6的等距双射与相位乘法恒等式给出等距代数同构；在该理想上，总变差范数本身具有常数一的次乘性。

取第二输入为 $\delta_x$，提升公式给出所述 $g_{\mu,f}$ 的逐点表达。它表明 $\mathcal T_\mu^{(t)}f$ 在每个 $H$ 纤维上恒定，而该函数由定理29.5连续。连续满射 $H$ 从紧空间到 Hausdorff 空间，因而是闭商映射。具体地，对闭集 $F\subseteq\mathbb R$，
$$
g_{\mu,f}^{-1}(F)=H\bigl((\mathcal T_\mu^{(t)}f)^{-1}(F)\bigr)
$$
为闭集，故 $g_{\mu,f}$ 连续。此结论不把截面本身称为连续映射。

归一化圆周 Haar 测度可取为 $[0,1)$ 上 Lebesgue 测度的商推前，因而无原子且质量为一。定理29.6保证其无原子提升唯一。圆周平移不变性及有符号积分给
$$
(m_{\mathbb T}*_{\mathbb T}\beta)(B)=\int_{\mathbb T}m_{\mathbb T}(B-\rho)\,d\beta(\rho)=m_{\mathbb T}(B)\beta(\mathbb T).
$$
对 $\beta=H_\#\mu$ 应用提升公式，得到 Haar 提升恒等式。$\lambda_K(K)=1$，所以共同理想非零；任一点质量不属于它，所以它是真理想。证毕。

**定理 29.8（全部有符号原子分解与连续柱集检测）。** 任意 $\mu\in M(K)$ 唯一分解为
$$
\mu=\mu_c+\mu_a,\qquad \mu_c\in M_c(K),\qquad \mu_a=\sum_{a\in A_\mu}\mu(\{a\})\delta_a,
$$
其中
$$
A_\mu=\{a\in K:\mu(\{a\})\ne0\}
$$
至多可数，级数在总变差范数中绝对收敛，并且
$$
\|\mu\|_{\mathrm{TV}}=\|\mu_c\|_{\mathrm{TV}}+\|\mu_a\|_{\mathrm{TV}},\qquad \|\mu_a\|_{\mathrm{TV}}=\sum_{a\in A_\mu}|\mu(\{a\})|.
$$
任意非零绝对可和原子测度 $\zeta$，都可由某个有限数字柱集的连续指示函数检测，即存在柱集 $U\subseteq K$ 使
$$
\mathbf1_U\in C(K),\qquad \langle\zeta,\mathbf1_U\rangle\ne0.
$$
特别，对任意绝对可和实序列 $(q_r)_{r\ge1}$，
$$
\left\|\sum_{r\ge1}q_rv_r\right\|_{\mathrm{TV}}=2\sum_{r\ge1}|q_r|,
$$
该和是正则有符号测度，且它对全部连续测试为零当且仅当每个 $q_r=0$。

**证明。** 对每个正整数 $j$，集合 $\{a:|\mu(\{a\})|\ge1/j\}$ 有限，否则有限子集上的变差可以任意大。因此 $A_\mu$ 可数。单点分割给
$$
\sum_{a\in A_\mu}|\mu(\{a\})|\le|\mu|(K).
$$
由有符号测度的可数可加性及该绝对可和性，$\mu_a$ 正是 $\mu$ 在可数 Borel 集 $A_\mu$ 上的限制，$\mu_c$ 则是其在补集上的限制。逐点检查得 $\mu_c(\{a\})=0$。两个限制的变差集中于互不相交的 Borel 集，故范数相加。唯一性由每个单点质量唯一确定全部原子系数而得。

一般地，若不同点 $z_i$ 的实系数满足 $\sum_i|d_i|<\infty$，则
$$
\zeta(D)=\sum_{z_i\in D}d_i
$$
可数可加，其正负系数部分集中于不交可数集，故
$$
|\zeta|(D)=\sum_{z_i\in D}|d_i|.
$$
这也直接证明总变差绝对收敛。正则性还可不依赖一般正则性定理而核对：对 Borel $D$，从 $D$ 内的原子选有限子集，使遗漏质量任意小，得到紧内逼近；从全部原子选有限集 $F$ 使尾质量任意小，则开集 $K\setminus(F\setminus D)$ 包含 $D$，并给出同样小的外误差。

若 $\zeta\ne0$，选 $z$ 使 $d_z\ne0$，再选包含 $z$ 的有限原子集 $F$，使
$$
\sum_{y\notin F}|d_y|<|d_z|/2.
$$
每个 $F\setminus\{z\}$ 中的点与 $z$ 在某个有限位不同。取足够长的 $z$ 的前缀，其柱集 $U$ 包含 $z$ 而排除 $F\setminus\{z\}$。柱集在数字拓扑中既开又闭，所以 $\mathbf1_U$ 连续，且
$$
\left|\int_K\mathbf1_U\,d\zeta\right|\ge|d_z|-\sum_{y\notin F}|d_y|>|d_z|/2>0.
$$
因此无限原子的正负尾项也不能使所有连续测试同时看不见这个非零测度。

不同 $E_r$ 互异，每对 $x_r^+,x_r^-$ 中两点不同，故不同 $v_r$ 的有限二点支撑两两不交。将上述变差公式用于这些实际原子，就得到最后的准确范数公式及检测结论。这里比较的是各原子的实际系数，不要求无限原子集合的拓扑闭包彼此分离。

最后，若 $\eta\in M_c(K)$ 而 $\zeta$ 为可数原子测度，$|\eta|$ 对 $\zeta$ 的可数原子集为零，故
$$
\|\eta-\zeta\|_{\mathrm{TV}}=\|\eta\|_{\mathrm{TV}}+\|\zeta\|_{\mathrm{TV}}.
$$
因此非零无原子测度不可能由原子测度在总变差范数中逼近。证毕。

**定理 29.9（完整原子测度的两个单侧极限与精确跳跃）。** 设 $\sigma\in M(K)$ 为任意可数原子测度，并记
$$
\beta=H_\#\sigma,\qquad b_\lambda=\beta(\{\lambda\}),\qquad \sum_\lambda|b_\lambda|\le\|\sigma\|_{\mathrm{TV}}.
$$
对每个 $\theta\in\mathbb T$，存在两条非分裂输入序列 $y_n^+,y_n^-$，其相位分别从严格正侧、负侧趋于 $\theta$，使
$$
\sigma\star_t\delta_{y_n^s}\longrightarrow R_\theta^s:=\sum_\lambda b_\lambda\delta_{s_s(\lambda+\theta)}\quad\text{于 }\sigma(M(K),C(K)),\qquad s\in\{+1,-1\}.
$$
若 $\theta\notin E$，两条输入序列均趋于 $k_\theta$；若 $\theta=E_j$，则分别趋于 $x_j^+$、$x_j^-$。两个极限测度及其差都是正则有符号测度，且
$$
\|R_\theta^s\|_{\mathrm{TV}}\le\|\beta\|_{\mathrm{TV}},\qquad J_\theta:=R_\theta^+-R_\theta^-=\sum_{r\ge1}b_{E_r-\theta}v_r,
$$
$$
\|J_\theta\|_{\mathrm{TV}}=2\sum_{r\ge1}|b_{E_r-\theta}|\le2\|\beta\|_{\mathrm{TV}}.
$$

**证明。** 令 $A=\{a:\sigma(\{a\})\ne0\}$，这是实际原子集合，不是其可能更大的拓扑闭包。集合
$$
F_\sigma=E\cup\bigcup_{a\in A}(E-H(a))
$$
可数。对每个 $n\ge1$ 和每个符号 $s$，可选
$$
0<\epsilon_n^s<\min(1/4,1/n),\qquad \theta_n^s=\theta+[s\epsilon_n^s]\notin F_\sigma,
$$
因为非空圆周开弧不可能由可数集合耗尽。定义 $y_n^s=k_{\theta_n^s}$。若 $\theta$ 非分裂，紧致性及唯一纤维保证任意这些提升趋于 $k_\theta$：任何子列聚点都必须落在该唯一纤维。若 $\theta=E_j$，假设29.1的严格单侧任意提升结论给出对应的定向极限。

对每个实际原子 $a$，$H(a)+\theta_n^s\notin E$，所以实际核行准确为
$$
P_t(a,y_n^s)=\delta_{k_{H(a)+\theta_n^s}}.
$$
在逐集合积分中对可数原子求和，并按相位 regroup，得到
$$
\sigma\star_t\delta_{y_n^s}=\sum_\lambda b_\lambda\delta_{k_{\lambda+\theta_n^s}}.
$$
重排合法，因为原始系数的绝对和不超过 $\|\sigma\|_{\mathrm{TV}}$。特别，同一相位上的正负分支在此处以它们的完整相位质量相加，不能遗漏这种抵消。

对每个固定 $\lambda$，相位 $\lambda+\theta_n^s$ 以同一严格符号趋于 $\lambda+\theta$。若极限相位非分裂，其唯一提升给出收敛；若它是 $E_r$，严格单侧提升给出收敛至 $x_r^s$。因此对任意 $f\in C(K)$，
$$
f(k_{\lambda+\theta_n^s})\longrightarrow f(s_s(\lambda+\theta)).
$$
各项由 $\|f\|_\infty|b_\lambda|$ 支配，而该系数族绝对可和。对级数使用支配收敛，得到声明的全部连续测试极限。定理29.8保证这些绝对可和原子和是实际正则测度。

两个截面只在 $E$ 上不同，所以极限差仅保留 $\lambda+\theta=E_r$ 的项，准确地给出 $J_\theta$。指标 $r$ 对应互异相位 $E_r-\theta$，故系数绝对和不超过 $\|\beta\|_{\mathrm{TV}}$；再用定理29.8的二点差分变差公式，得到准确范数。所有极限均为连续测试意义的弱星极限，不声称总变差收敛。证毕。

**定理 29.10（任意实有符号原子的排除与拓扑中心完全分类）。** 在假设29.1下，对每个 $t\in\Lambda$，
$$
Z_{\mathrm{top}}(\star_t)=M_c(K).
$$
更具体地，若 $\mu$ 的原子部分非零，则存在有限数字柱集 $U$、点 $x\in K$ 及序列 $x_n\to x$，使
$$
\mathcal T_\mu^{(t)}\mathbf1_U(x_n)\not\longrightarrow\mathcal T_\mu^{(t)}\mathbf1_U(x).
$$
结论包括总质量为零、相位推前原子部分为零以及同一分裂纤维正负质量抵消的情形，也包括参数 $0$ 与形式参数 $\infty$。

**证明。** 无原子的充分性已经由定理29.5证明。拓扑中心是线性子空间，因为定理29.4中的连续函数条件对线性组合封闭。若 $\mu$ 属于拓扑中心，作定理29.8的分解 $\mu=\mu_c+\sigma$，其中 $\sigma=\mu_a$。由于 $\mu_c$ 已在中心中，$\sigma$ 也在中心中。因此必要性归结为证明：中心中的可数原子测度只能为零。

先对 $\sigma$ 使用定理29.9，记其完整相位质量为 $b_\lambda$。若 $\theta\notin E$，两条输入序列均趋于同一点 $k_\theta$。弱星连续性使它们的输出极限相同，故 $J_\theta=0$。由于 $J_\theta$ 是总变差绝对可和的正则原子测度，定理29.8给出
$$
b_{E_r-\theta}=0\qquad(r\ge1,\ \theta\notin E).
$$
现固定 $\lambda\notin\mathcal O_+$，取 $\theta=E_1-\lambda$。这个 $\theta$ 不属于 $E$：否则 $\theta=E_j$ 会推出
$$
\lambda=E_1-E_j=[(j-1)\phi]\in\mathcal O_+,
$$
矛盾。上式取 $r=1$ 得 $b_\lambda=0$。所以完整相位原子质量只能留在非负整数旋转轨道 $\mathcal O_+$ 上。

由于 $\phi$ 无理，$E\cap\mathcal O_+=\varnothing$，故每个分裂纤维的完整相位质量已经为零。非分裂纤维只有一个点，且 $[n\phi]$ 的唯一点为 $Z(n)$。因此 $\sigma$ 必有准确展开
$$
\sigma=\sum_{n\ge0}b_n\delta_{Z(n)}+\sum_{m\ge1}a_mv_m,
$$
$$
b_n=\sigma(\{Z(n)\}),\qquad a_m=\sigma(\{x_m^+\})=-\sigma(\{x_m^-\}),\qquad \|\sigma\|_{\mathrm{TV}}=\sum_{n\ge0}|b_n|+2\sum_{m\ge1}|a_m|.
$$
第一项保留全部尚未排除的相位原子，第二项保留相位推前完全看不见的分支差分；两者不能混同。

固定 $j\ge1$。定理29.9在输入相位 $E_j$ 给出
$$
R_{E_j}^s=\sum_{n=0}^{j-1}b_n\delta_{x_{j-n}^s}+\sum_{n\ge j}b_n\delta_{Z(n-j)},
$$
因为 $[n\phi]+E_j=E_{j-n}$ 当 $n<j$，而当 $n\ge j$ 时该相位为 $[(n-j)\phi]$。置
$$
Q_j=\sum_{n=0}^{j-1}b_n\pi_{E_{j-n}}+\sum_{n\ge j}b_n\delta_{Z(n-j)},\qquad W_j=\sum_{m\ge1}a_mc_{m,j}v_{m+j}.
$$
这两个和都是总变差绝对收敛的实际测度。对 $Q_j$，使用 $\|\pi_\theta\|_{\mathrm{TV}}\le C_t$。对 $W_j$，有限差分恒等式及定理29.2给
$$
2|c_{m,j}|=\|v_m\star_t v_j\|_{\mathrm{TV}}\le C_t\|v_m\|_{\mathrm{TV}}\|v_j\|_{\mathrm{TV}}=4C_t,
$$
所以 $\sum_m|a_mc_{m,j}|<\infty$。

实际两个分支行必须由第25节的有限核恒等式逐项积分计算，而不是由单侧极限指定。具体地，$\delta_{Z(n)}=\pi_{[n\phi]}$，混合相位差分乘积为零，且
$$
\delta_{x_j^+}=\pi_{E_j}+(1-p_j)v_j,\qquad \delta_{x_j^-}=\pi_{E_j}-p_jv_j.
$$
因此直接对上述绝对可和原子系数积分，得到
$$
\sigma\star_t\delta_{x_j^+}=Q_j+(1-p_j)W_j,\qquad \sigma\star_t\delta_{x_j^-}=Q_j-p_jW_j.
$$
逐项积分的绝对收敛由统一行界与 $\sum_n|b_n|+2\sum_m|a_m|<\infty$ 保证。这特别给出不含任何 $p_j$ 分母的准确差值
$$
\sigma\star_t\delta_{x_j^+}-\sigma\star_t\delta_{x_j^-}=W_j.
$$

由于 $\sigma$ 在中心中，分别趋于 $x_j^+$ 与 $x_j^-$ 的单侧输入序列必须趋于各自的实际输出行。相减得到
$$
\sum_{m\ge1}a_mc_{m,j}v_{m+j}=\sum_{n=0}^{j-1}b_nv_{j-n}.
$$
左边的原子对指标严格大于 $j$，右边的指标介于一与 $j$。不同指标的二点支撑不交；即使无限原子集的闭包有共同聚点，也不会改变单点质量。定理29.8因此给出准确的缺陷范数
$$
\left\|W_j-\sum_{n=0}^{j-1}b_nv_{j-n}\right\|_{\mathrm{TV}}=2\sum_{m\ge1}|a_mc_{m,j}|+2\sum_{n=0}^{j-1}|b_n|.
$$
中心条件使该范数为零。取 $j=1$，由于每个 $c_{m,1}\ne0$，得到全部 $a_m=0$，同时得到 $b_0=0$。再对任意 $n\ge0$ 取 $j=n+1$，得到 $b_n=0$。因此 $\sigma=0$，必要性成立。

这里 $c_{m,j}\ne0$ 对所有允许的有限实参数由定理25.7给出；参数 $0$ 时 $c_{m,j}=1$，形式参数 $\infty$ 时 $c_{m,j}=-1$。整个排除过程没有除以 $p_j$ 或 $1-p_j$，也没有要求任何原子系数或核系数为正。

最后核对声明的实际连续测试见证，而不只给出形式系数矛盾。给定非零原子测度 $\sigma$，若某个非零 $b_\lambda$ 位于 $\mathcal O_+$ 外，取上述 $\theta=E_1-\lambda$，则 $J_\theta$ 在 $v_1$ 上的系数非零。定理29.8给出连续柱集指示函数 $f$ 使 $\langle J_\theta,f\rangle\ne0$。两条输入序列趋于同一 $k_\theta$，而其标量输出极限不同，故至少一条不趋于实际行在该点的测试值。

若全部完整相位质量均在 $\mathcal O_+$ 上，则 $\sigma$ 具有上面的 $b_n,a_m$ 展开。若某个 $a_m\ne0$，取 $j=1$；否则选 $b_n\ne0$ 并取 $j=n+1$。准确缺陷范数表明
$$
D_j:=W_j-(R_{E_j}^+-R_{E_j}^-)\ne0.
$$
再用定理29.8选连续柱集指示函数 $f$ 检测 $D_j$。两个实际行与两个对应单侧极限不可能同时在该测试上相等，因为两种差值的差正是 $\langle D_j,f\rangle\ne0$。所以至少一个定向分裂输入处有标量不连续。

对于原始测度 $\mu=\mu_c+\sigma$，定理29.5保证 $\mathcal T_{\mu_c}^{(t)}f$ 连续；把它加回不会消除上述实际行与其单侧极限之间的非零差。于是同一个连续柱集测试也检测 $\mu$ 的不连续性。这覆盖了所有可数有符号抵消情形。证毕。

**定理 29.11（任意柱集中的无原子逼近与弱星稠密性）。** 每个非空有限数字柱集都支持一个无原子概率测度。对任意 $\mu\in M(K)$，存在 $\mu_N\in M_c(K)$，使
$$
\|\mu_N\|_{\mathrm{TV}}\le\|\mu\|_{\mathrm{TV}},\qquad \mu_N(K)=\mu(K),\qquad \mu_N\longrightarrow\mu\text{ 于 }\sigma(M(K),C(K)).
$$
因此该共同拓扑中心虽然是总变差闭真理想，却在全测度空间中弱星稠密。

**证明。** 固定长度为 $N$ 的合法前缀 $w$，记其非空柱集为 $C_w$。对 $u\in[0,1)$，定义二进制数字
$$
\epsilon_r(u)=\lfloor2^{r+1}u\rfloor-2\lfloor2^ru\rfloor\in\{0,1\}\qquad(r\ge0).
$$
构造 $q_w(u)\in K$：前 $N$ 位取 $w$，第 $N$ 位取零，并令
$$
q_w(u)_{N+1+2r}=\epsilon_r(u),\qquad q_w(u)_{N+2+2r}=0\qquad(r\ge0).
$$
前缀与自由尾部之间有一个零，尾部任意两个自由位之间也有零，所以所有输出均合法并属于 $C_w$。每个坐标是 Borel 函数，柱集生成数字 Borel 结构，故 $q_w$ 为 Borel 映射。令 $\xi_w$ 为 $[0,1)$ 上 Lebesgue 概率测度在 $q_w$ 下的推前。它是有限正则概率测度，并集中于 $C_w$。

对任意固定点 $z\in K$，条件 $q_w(u)=z$ 会指定前 $r$ 个二进制数字，因此其原像至多包含在一个长度为 $2^{-r}$ 的半开二进制区间内，或为空。于是
$$
\xi_w(\{z\})\le2^{-r}\qquad(r\ge1),
$$
从而 $\xi_w(\{z\})=0$。这证明每个实际柱集内都有所需无原子概率测度。

令 $\mathcal W_N$ 为长度 $N$ 的全部合法前缀，定义
$$
\mu_N=\sum_{w\in\mathcal W_N}\mu(C_w)\xi_w.
$$
这是有限个无原子测度的实线性组合，所以仍无原子。柱集构成有限 Borel 分割，故
$$
\|\mu_N\|_{\mathrm{TV}}\le\sum_{w\in\mathcal W_N}|\mu(C_w)|\le\|\mu\|_{\mathrm{TV}},\qquad \mu_N(K)=\sum_w\mu(C_w)=\mu(K).
$$
对 $f\in C(K)$，令
$$
\omega_f(r)=\sup\{|f(x)-f(y)|:d_K(x,y)\le r\}.
$$
紧致性使 $f$ 一致连续，所以 $\omega_f(r)\to0$ 当 $r\downarrow0$。每个 $C_w$ 的直径至多为 $2^{-N}$，于是
$$
\begin{aligned}
|\langle\mu_N-\mu,f\rangle|&=\left|\sum_w\int_{C_w}\left(\int_{C_w}f(y)\,d\xi_w(y)-f(x)\right)d\mu(x)\right|\\
&\le\omega_f(2^{-N})\sum_w|\mu|(C_w)\\
&=\omega_f(2^{-N})\|\mu\|_{\mathrm{TV}}\longrightarrow0.
\end{aligned}
$$
因此对全部连续测试弱星收敛。总变差闭性和真性来自定理29.7，拓扑中心识别来自定理29.10。此稠密性不把非中心元素的左乘算子变成弱星连续算子；定理29.10仍为每个非零原子部分提供实际连续测试障碍。证毕。

[^rro29-riesz]: Martin Herdegen, Gechun Liang and Osian Shelley, *Vague and weak convergence of signed measures*, arXiv:2205.13207v2，§1.1，Definition 1.1 与 Theorem 1.2(a)。这里引用连续测试收敛、有限有符号 Radon 测度及 Riesz 等距表示。[正文](https://arxiv.org/html/2205.13207v2)。

[^rro29-kernel]: Vassili N. Kolokoltsov, *Stochastic monotonicity and duality of kth order with application to put-call symmetry of powered options*, arXiv:1405.3894v1，§2.2，特别有界有符号核的定义、积分算子与测度对偶公式及 Proposition 2.1 的 Fubini 计算。[正文](https://arxiv.org/html/1405.3894v1)。

[^rro29-integration]: Terence Tao, *245B, notes 0: A quick review of measure and integration theory*，2009年1月1日，Theorem 3(4)—(5) 与 Theorem 4，分别给出支配收敛、绝对可和级数积分与 Fubini–Tonelli 的可测性及绝对可积条件；*245B, notes 1: Signed measures and the Radon-Nikodym-Lebesgue theorem*，2009年1月4日，Hahn 分解、Exercises 5—8 的 Jordan 分解和总变差。本节对有符号测度的使用均明确化为有限正 Jordan 部分或变差测度。[积分正文](https://terrytao.wordpress.com/2009/01/01/245b-notes-0-a-quick-review-of-measure-and-integration-theory/)，[有符号测度正文](https://terrytao.wordpress.com/2009/01/04/245b-notes-1-signed-measures-and-the-radon-nikodym-lebesgue-theorem/)。

[^rro29-center]: Stefano Ferri, Matthias Neufang and Jan Pachl, *Minimal sets determining the topological centre of the algebra LUC(G)\**, arXiv:1310.7931v2，§1，Definition 1.1；这里仅采用左乘在指定弱星拓扑中全域连续的拓扑中心定义，不移用其关于其他代数的中心分类。[正文](https://arxiv.org/html/1310.7931v2)。

[^rro29-ideal]: Tetsuhiro Shimizu, *L-ideals of Measure Algebras*, Proceedings of the Japan Academy 48 (1972), 172–176，§1，特别第172—173页关于通常卷积测度代数及连续测度理想的记号。本节圆周上的无原子理想性质由逐单点卷积积分另行证明。[正文](https://www.jstage.jst.go.jp/article/pjab1945/48/3/48_3_172/_pdf/-char/ja)。

## 追加锚（本行以下为增补区）
