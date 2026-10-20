# FIB：任务族—分割 Galois 对偶与白盒闭包

> 本卷提出一个独立的纯数学层：把“哪些任务被保留”和“哪些状态能够合并”视为一对反变的对象。它不修改 [Fibonacci 原子关系生成卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md)。任务商、证书商、更新下降和未来闭包已有仓内来源；本卷把它们作为桥接材料，新增的候选内容集中在双侧闭包的统一视角、逃逸对的探针覆盖，以及这两者对 `101` 和机器学习白盒接口的应用。
>
>
> 本文只在有限状态、确定性读数和确定性更新的模型内推导。Galois 连接、Myhill–Nerode 型商和集合覆盖是成熟框架；它们在这里标为 `literature-attested`。仓内已有的商与未来闭包标为 `repo-derived`。把任务族—分割闭包、逃逸覆盖和学习合同放在同一接口中的差分目前保持 `open`，不能把它当作原创性证明。正文是普通数学文本，未声称 Lean 核验、真实神经网络实现或物理真实性。

### 0.1 来源与新意边界

| 内容 | 状态 | 本卷用途 |
|---|---|---|
| Galois 连接、等价关系闭包、Myhill–Nerode 型最小商、集合覆盖 | `literature-attested` | 通用数学工具；本卷只在有限接口模型中组合它们 |
| 任务行为商、证书保持商、更新下降和有限未来闭包 | `repo-derived`，见 [FIB 原子证书保持商](FIB_ATOM_CERTIFICATE_PRESERVING_QUOTIENT.md)、[关系纤维演算](FIB_RELATIONAL_FIBER_CALCULUS.md) 和 [递归观察边界三分](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md) | 作为已有定理的参数对应，不重复主张为新结果 |
| 任务族—状态分割的双侧闭包、逃逸对到非自适应探针覆盖的精确转换、学习读数与可执行更新的分合同 | `open`（文献差分尚未完成） | 本卷的候选增量，需以独立文献检索、反例、有限算例或后续形式化继续检验 |

因此，后文重复写出的商和未来闭包是“接合引理”，而不是独立的新颖性声明。当前不能把候选增量称为已确认原创。

### 0.2 文献定位

Galois 连接的格论背景可追溯至 Birkhoff 的 *Lattice Theory*（第 3 版，1967）；有限自动机的状态商与 Myhill–Nerode 理论见 Myhill 的 *Finite automata and the representation of events*（1957）和 Nerode 的 *Linear automaton transformations*（1958）；非自适应探针选择的加权集合覆盖属于 Karp 的 *Reducibility among combinatorial problems*（1972）所列组合优化框架。它们支撑本卷的通用工具，不支撑本卷关于 FIB 或机器学习接口的候选综合；后者仍保持 `open`。

## 1. 任务和分割是同一信息的两面

### 定义 1.1（有限状态与任务语言）

设 $S$ 是有限状态集。一个任务是一个确定性读数

$$
 f:S\to O_f,
$$

其中 $O_f$ 是该任务自己的有限输出集。任务语言 $\mathcal T$ 是一族允许使用的任务；它可以包含当前输出、失败标签、未来响应、更新读出或它们的联合读数。不同任务的输出集不要求相同。

对任意任务族 $\Gamma\subseteq\mathcal T$，定义其状态关系

$$
R_\Gamma
=
\bigcap_{f\in\Gamma}\ker f,
\qquad
s\mathrel{R_\Gamma}s'
\Longleftrightarrow
\forall f\in\Gamma,\ f(s)=f(s').
\tag{1.1}
$$

空任务族的交取为 $S\times S$。因为每个 $\ker f$ 都是等价关系，$R_\Gamma$ 也是等价关系。

反过来，对 $S$ 上的等价关系 $R$，定义在 $R$ 上可读出的任务族

$$
\mathcal T_R
=
\{f\in\mathcal T:R\subseteq\ker f\}.
\tag{1.2}
$$

这表示所有在 $R$ 的每个纤维上恒定的允许任务。

### 定理 1.2（任务—分割 Galois 对偶）

对任意任务族 $\Gamma\subseteq\mathcal T$ 和等价关系 $R$，有

$$
\boxed{
\Gamma\subseteq\mathcal T_R
\quad\Longleftrightarrow\quad
R\subseteq R_\Gamma.
}
\tag{1.3}
$$

因此，增加任务只会细化状态分割，而要求更多任务在摘要上可读只会细化允许的状态分割。

**证明。**

$$
\Gamma\subseteq\mathcal T_R
\Longleftrightarrow
\forall f\in\Gamma,\ R\subseteq\ker f
\Longleftrightarrow
R\subseteq\bigcap_{f\in\Gamma}\ker f
=R_\Gamma.
$$

证毕。

### 定义 1.3（两侧闭包）

在固定任务语言 $\mathcal T$ 下，定义

$$
\operatorname{cl}_{\mathcal T}(\Gamma)=\mathcal T_{R_\Gamma},
$$

以及

$$
\operatorname{cl}_{\mathrm{rel}}(R)=R_{\mathcal T_R}.
$$

第一者补全由 $\Gamma$ 的状态纤维已经决定的全部允许任务；第二者补全在当前任务语言中可被区分的全部关系。

### 定理 1.4（闭包律）

两侧闭包满足：

1. $\Gamma\subseteq\operatorname{cl}_{\mathcal T}(\Gamma)$；
2. $R\subseteq\operatorname{cl}_{\mathrm{rel}}(R)$；
3. 若 $\Gamma_1\subseteq\Gamma_2$，则
   $$
   \operatorname{cl}_{\mathcal T}(\Gamma_1)
   \subseteq
   \operatorname{cl}_{\mathcal T}(\Gamma_2);
   $$
4. 若 $R_1\subseteq R_2$，则
   $$
   \operatorname{cl}_{\mathrm{rel}}(R_1)
   \subseteq
   \operatorname{cl}_{\mathrm{rel}}(R_2);
   $$
5. 两侧闭包都是幂等的。

**证明。** 前四项直接由定理 1.2 的反变对应得到。以任务侧为例，$f\in\Gamma$ 时显然 $R_\Gamma\subseteq\ker f$，故 $f\in\mathcal T_{R_\Gamma}$；包含关系给出任务侧单调性。若 $R_1\subseteq R_2$，则 $\mathcal T_{R_2}\subseteq\mathcal T_{R_1}$，取任务核的交集得到 $\operatorname{cl}_{\mathrm{rel}}(R_1)\subseteq\operatorname{cl}_{\mathrm{rel}}(R_2)$。再次取状态关系时，$R_{\mathcal T_{R_\Gamma}}$ 与 $R_\Gamma$ 在任务语言能观察到的部分相同，因此两侧闭包都幂等。证毕。

### 推论 1.5（白盒性是闭合对，不是单独属性）

一个表示的白盒性必须同时指定：

$$
\boxed{
(\text{允许任务族 }\Gamma,\ \text{其状态关系 }R_\Gamma).
}
$$

同一个内部状态摘要，在两个不同任务语言下可以分别是充分的和不充分的；同一个任务语言下，两个摘要若诱导同一个闭合任务族，则对该语言不可区分。

“模型本身是否白盒”没有脱离任务语言的单独真值。

## 2. 任务相关的规范最小商

### 定义 2.1（任务商）

令

$$
\eta_\Gamma:S\to S/R_\Gamma,
\qquad
\eta_\Gamma(s)=[s]_{R_\Gamma}.
$$

称 $\eta_\Gamma$ 为任务族 $\Gamma$ 的规范商。

### 定理 2.2（任务族的最小充分摘要）

摘要 $q:S\to Q$ 能准确支持任务族 $\Gamma$ 的全部读数，当且仅当

$$
\ker q\subseteq R_\Gamma.
\tag{2.1}
$$

在此条件下，每个 $f\in\Gamma$ 都唯一下降为

$$
\overline f:q(S)\to O_f,
\qquad
f=\overline f\circ q.
$$

并且存在唯一满射

$$
 h:q(S)\twoheadrightarrow S/R_\Gamma
$$

满足

$$
 h(q(s))=\eta_\Gamma(s).
$$

因此

$$
\boxed{|q(S)|\ge |S/R_\Gamma|.}
\tag{2.2}
$$

商 $\eta_\Gamma$ 达到下界。

**证明。** 若 $q(s)=q(s')$，由 (2.1) 得 $f(s)=f(s')$，所以在每个摘要纤维上任选代表元即可定义 $\overline f$，且定义与代表元无关。相同论证定义 $h(q(s))=[s]_{R_\Gamma}$；它良定义并满射。基数不等式来自满射。反过来，$\eta_\Gamma$ 本身使每个 $f\in\Gamma$ 在等价类上恒定，所以达到下界。证毕。

### 定理 2.3（任务细化的规范映射）

若 $\Gamma\subseteq\Lambda\subseteq\mathcal T$，则

$$
R_\Lambda\subseteq R_\Gamma
$$

并存在规范满射

$$
 p_{\Lambda,\Gamma}:S/R_\Lambda\twoheadrightarrow S/R_\Gamma,
\qquad
p_{\Lambda,\Gamma}([s]_{R_\Lambda})=[s]_{R_\Gamma}.
$$

这些满射满足

$$
 p_{\Gamma,\Gamma}=\mathrm{id},
\qquad
 p_{\Lambda,\Gamma}\circ p_{\Omega,\Lambda}=p_{\Omega,\Gamma}
$$

只要 $\Gamma\subseteq\Lambda\subseteq\Omega$。

**证明。** 交集中的任务越多，关系越细。若 $sR_\Lambda s'$，则 $sR_\Gamma s'$，所以映射良定义；每个 $R_\Gamma$ 类都有代表元，故满射。恒等式在代表元上直接成立。证毕。

这说明任务增加不是“重新训练出一个新名字”，而是在同一个状态集合上沿满射反向细化商。任务读数的增量正是新任务切开的旧纤维。

### 命题 2.4（有限语言中的可观测闭包）

若 $\mathcal T$ 包含所有二值任务 $1_{\{s\}}$ 的有限组合，则

$$
\operatorname{cl}_{\mathrm{rel}}(R)=R
$$

对任意等价关系 $R$ 成立。若 $\mathcal T$ 是受限的，则可能有

$$
R\subsetneq\operatorname{cl}_{\mathrm{rel}}(R).
$$

**证明。** 若 $s\not R s'$，取一个 $R$-类 $C$ 包含 $s$ 而不包含 $s'$，其指示函数在 $R$ 的每个类上恒定，并且区分 $s,s'$，所以 $(s,s')\notin R_{\mathcal T_R}$。故关系侧闭包不增大。一般包含关系来自定义。受限语言缺少区分某些纤维的任务时，严格包含可以发生。证毕。

这是一个关键边界：全函数语言下的“最小商”是纯集合事实；真正的白盒问题还包括哪些任务在物理、训练或接口上被允许取得。

## 3. 把未来和更新纳入同一个闭包

本节是对仓内未来响应商和最大安全同余结果的抽象接合，采用它们的结论作为 `repo-derived` 前提；新意不在重新证明有限闭合，而在后面的探针覆盖和学习合同分解。

### 定义 3.1（动作和任务的未来展开）

设 $A$ 是有限动作集，每个 $a\in A$ 诱导确定性更新 $U_a:S\to S$。对词 $\alpha=a_1\cdots a_k$，令 $U_\alpha$ 为按时间顺序复合的更新，空词为恒等。

给定任务族 $\Gamma$，定义未来展开

$$
\Gamma^{\uparrow}
=
\{f\circ U_\alpha:f\in\Gamma,\ \alpha\in A^*\}.
\tag{3.1}
$$

若更新合同还要求读取一个状态量 $\chi:S\to Z$，把所有 $\chi\circ U_\alpha$ 加入同一个任务族；若需要完整失败边，就把失败边的指示任务加入。

### 定理 3.2（未来任务闭包的等价形式）

未来展开的关系为

$$
R_{\Gamma^{\uparrow}}
=
\bigcap_{\alpha\in A^*}(U_\alpha\times U_\alpha)^{-1}(R_\Gamma).
\tag{3.2}
$$

它是包含于 $R_\Gamma$ 的最大、对所有 $U_a$ 稳定的等价关系。

**证明。** 等式由

$$
(f\circ U_\alpha)(s)=(f\circ U_\alpha)(s')
\Longleftrightarrow
(U_\alpha(s),U_\alpha(s'))\in\ker f
$$

逐项取交得到。若 $sR_{\Gamma^{\uparrow}}s'$，对任意 $a$ 和任意 $\alpha$，有

$$
U_\alpha(U_a(s))=U_{a\alpha}(s),
$$

故 $U_a(s)R_{\Gamma^{\uparrow}}U_a(s')$，所以稳定。若 $E\subseteq R_\Gamma$ 是稳定等价关系，则对任意词 $\alpha$ 归纳得到 $(U_\alpha(s),U_\alpha(s'))\in R_\Gamma$，故 $E\subseteq R_{\Gamma^{\uparrow}}$。证毕。

### 推论 3.3（闭包迭代和有限终止）

定义

$$
R_0=R_\Gamma,
\qquad
R_{n+1}=R_\Gamma\cap\bigcap_{a\in A}(U_a\times U_a)^{-1}(R_n).
\tag{3.3}
$$

在有限 $S$ 上，$R_n$ 在至多 $|S|-|S/R_0|$ 次严格细化后稳定，并且稳定值等于 $R_{\Gamma^{\uparrow}}$。

**证明。** 归纳展开 (3.3) 可知 $R_n$ 恰要求长度不超过 $n$ 的未来词上的所有任务相同。每次严格细化至少增加一个等价类，故在给定界内稳定。稳定值既对所有单步更新闭合，也包含于 $R_\Gamma$；定理 3.2 的最大性给出两者相等。证毕。

### 定理 3.4（公共白盒商的单族表达）

设 $\Gamma_{\mathrm{beh}}$、$\Gamma_{\mathrm{cert}}$ 和 $\Gamma_{\mathrm{upd}}$ 分别是行为、完整证书和更新合同的当前任务族。令

$$
\Gamma_*=
\Gamma_{\mathrm{beh}}^{\uparrow}
\cup
\Gamma_{\mathrm{cert}}^{\uparrow}
\cup
\Gamma_{\mathrm{upd}}^{\uparrow}.
$$

则

$$
R_{\Gamma_*}
=R_{\mathrm{beh}}^{\uparrow}
\cap R_{\mathrm{cert}}^{\uparrow}
\cap R_{\mathrm{upd}}^{\uparrow}.
\tag{3.4}
$$

因此行为—证书—更新的共同最小商，等价于一个任务语言下的普通规范商；所谓“多层白盒接口”只是在同一 Galois 闭包中加入不同任务源。

**证明。** 对任意任务族，关系映射把并集送到交集：

$$
R_{\Gamma_1\cup\Gamma_2}=R_{\Gamma_1}\cap R_{\Gamma_2}.
$$

对三个未来展开应用此恒等式即可。证毕。

这不是把三种语义混为一谈：它说明它们可以由任务标签分层保留，同时在数学上汇合到一个公共关系。

## 4. 逃逸见证与最小探针覆盖

### 定义 4.1（逃逸对和任务覆盖）

给定当前关系 $R_0$ 和目标关系 $R_*\subseteq R_0$，定义待切开的无序对集合

$$
\mathcal P(R_0,R_*)
=\{\{s,s'\}:sR_0s',\ \neg(sR_*s'),\ s\ne s'\}.
\tag{4.1}
$$

对任务 $f\in\mathcal T$，定义其覆盖集

$$
C_f=\{\{s,s'\}\in\mathcal P(R_0,R_*):f(s)\ne f(s')\}.
\tag{4.2}
$$

任务族 $H\subseteq\mathcal T$ 是一个**非自适应分离族**，如果

$$
R_0\cap\bigcap_{f\in H}\ker f\subseteq R_*.
\tag{4.3}
$$

### 定理 4.2（探针选择的精确覆盖判据）

对有限 $\mathcal P(R_0,R_*)$，任务族 $H$ 满足 (4.3)，当且仅当

$$
\bigcup_{f\in H}C_f=\mathcal P(R_0,R_*).
\tag{4.4}
$$

所以最少探针数是集合覆盖数。若任务语言或候选探针有限，且费用 $c(f)\ge0$，最低总费用是达到的加权集合覆盖最小值；在一般无限语言中只能定义为下确界，未必有达到下确界的探针族。

**证明。** 若 (4.4) 失败，存在一对 $\{s,s'\}$ 不被任何 $f\in H$ 区分，于是 $s,s'$ 属于左侧交集而不属于 $R_*$，违反 (4.3)。反之，若左侧交集中有 $s,s'$，则它们在 $R_0$ 中相等；若不在 $R_*$ 中，就属于 $\mathcal P$，应被某个 $C_f$ 覆盖，和 $f(s)=f(s')$ 矛盾。证毕。

### 推论 4.3（探针复杂度和语义状态数是不同坐标）

规范商的状态数

$$
\sigma(\Gamma)=|S/R_\Gamma|
$$

只测量必须区分多少语义状态；定理 4.2 的覆盖费用测量取得这些区别需要问多少任务。二者不能由一个标量互相替代。

若允许自适应任务树，任意非自适应覆盖族都可以按固定顺序逐项询问，因此给出深度至多 $|H|$ 的决策树上界；不能在没有额外分支假设时称为平衡树。自适应树可能更便宜，但它增加了“下一任务依赖此前回答”的控制合同，不能把集合覆盖数直接称为自适应最优值。

### 命题 4.4（任务冗余的局部判据）

在当前关系 $R$ 下，任务 $f$ 对一个已有任务族 $\Gamma$ 是冗余的，当且仅当

$$
R_\Gamma\subseteq\ker f.
\tag{4.5}
$$

否则，任意一对 $sR_\Gamma s'$ 且 $f(s)\ne f(s')$ 都是一个新增逃逸见证，并且加入 $f$ 后关系严格细化。

**证明。** (4.5) 正是 $f\in\mathcal T_{R_\Gamma}$ 的定义。若不成立，取反例对即可；新交集删去该对，故严格细化。证毕。

这给出一种严格的 probe triage：先检查候选任务是否切开当前纤维，再决定它是否值得加入任务语言。重复读取一个已闭合任务不会增加白盒信息。

## 5. FIB 的 `101`：一个一维关系纤维如何被切开

### 命题 5.1（四点训练读数留下唯一联合方向）

令

$$
\Sigma=\{000,100,010,101,001\}
$$

为合法窗口，令 $\mathcal V=\{f:\Sigma\to\mathbb R\}$。每个 $f\in\mathcal V$ 唯一表示为

$$
 f(b)=c_0+c_1b_1+c_2b_2+c_3b_3+c_{13}b_1b_3,
\tag{5.1}
$$

其中

$$
 c_{13}=f(101)-f(100)-f(001)+f(000).
\tag{5.2}
$$

令训练任务族为

$$
\Gamma_0=\{\operatorname{ev}_{000},\operatorname{ev}_{100},
\operatorname{ev}_{010},\operatorname{ev}_{001}\}.
$$

则两个函数在 $\Gamma_0$ 下等价，当且仅当它们的差是

$$
\lambda h,
\qquad
h(101)=1,
\quad
h(000)=h(100)=h(010)=h(001)=0.
\tag{5.3}
$$

加入任务 $\operatorname{ev}_{101}$ 后，关系变为恒等关系。

**证明。** 四个已知点的取值依次唯一确定 $c_0,c_1,c_2,c_3$；唯一未确定的系数是 $c_{13}$，其变化正好产生 (5.3) 的方向。$\operatorname{ev}_{101}$ 直接读取该方向，所以其核与 $R_{\Gamma_0}$ 的交只含零差。证毕。

这里 `101` 不是“第五个标签”这一统计命名，而是覆盖了训练纤维中唯一未切开的联合关系方向。若训练任务只看到四个 proper 点，零训练误差只说明落在同一纤维内；它不说明联合关系已经被识别。

### 推论 5.2（低阶摘要的未来逃逸）

若某个摘要只保持 $\Gamma_0$ 的读数，而允许的未来任务包含 $\operatorname{ev}_{101}$ 或任何对该联合方向敏感的 continuation，则定理 4.2 给出一个单任务逃逸见证。任何只依赖当前摘要的未来读出，至少在同一纤维中的两个函数之一上错误。

作为一个有明确范围的形式化来源，[`native_probability_separation`](../../../D5/S3/Arith/FibonacciAtomic/NativeContinuation/JointLaw.lean) 在已初始化的合法固定长度来源、$n\ge3$、$0<\mathrm{mix}<1$，并在声明的 proper seam 读数域和正质量条件下，给出一组 proper seam 联合报告、固定线性读数和最终期望相同、但追加合法 continuation 后精确 reply 分布不同的实例。这里仅使用其适用范围内的实例，不把它推广到任意来源。

## 6. 机器学习白盒性作为闭合任务对

### 定义 6.1（学习合同）

令 $\Theta$ 是模型内部状态集，$P:\Theta\to Y$ 是当前预测读出，$U_a:\Theta\to\Theta$ 是训练或干预动作，$\chi:\Theta\to Z$ 是需要保留的优化器或更新读出。给定允许的当前任务集合 $\mathcal G$，先取其未来展开

$$
\mathcal G^{\uparrow}=\{g\circ U_\alpha:g\in\mathcal G,\ \alpha\in A^*\},
$$

再定义学习合同族

$$
\Gamma_{\mathrm{learn}}
=\mathcal G^{\uparrow}
\cup\{P\circ U_\alpha:\alpha\in A^*\}
\cup\{\chi\circ U_\alpha:\alpha\in A^*\}.
\tag{6.1}
$$

若需要认证失败边，则把其指示任务加入 $\mathcal G$，而不是只记录一个失败计数。

### 定理 6.2（白盒摘要的闭合判据）

摘要 $q:\Theta\to Q$ 是学习合同下的精确白盒接口，当且仅当读数合同和可执行更新合同都成立：

1. **读数合同：**
   $$
   \ker q\subseteq R_{\Gamma_{\mathrm{learn}}};
   $$
2. **可执行更新合同：** 对每个动作 $a$ 存在 $\overline U_a:q(\Theta)\to q(\Theta)$，使
   $$
   q\circ U_a=\overline U_a\circ q;
   $$
在这些条件下，当前预测、允许干预、训练后的预测、优化器读出和认证任务都唯一下降到 $q(\Theta)$ 上。若读数合同失败，则存在同一摘要纤维中被某个合同任务区分的逃逸对；若更新合同失败，则存在同一摘要值产生不同后继摘要的更新见证。若任务没有被放入 $\Gamma_{\mathrm{learn}}$，这只是合同边界未声明，不能反推为状态逃逸。

**证明。** 读数合同是定理 2.2 对已经未来展开的任务族的直接应用。可执行更新合同等价于 $\ker q\subseteq\ker(q\circ U_a)$，因此 $\overline U_a$ 良定义；按动作词归纳得到所有 $U_\alpha$ 的交换式。反过来，若摘要能准确回答合同中的全部读数，则同摘要状态必须对每个合同任务给出相同结果，故 $\ker q\subseteq R_{\Gamma_{\mathrm{learn}}}$；若某个动作不能下降，则同一摘要值会产生两个不同后继摘要，违反确定性接口。证毕。

### 例 6.3（当前函数商和训练商的差异）

取 $f_{a,b}(x)=abx$，平方损失 $L=\frac12(abx-y)^2$，并以固定步长 $\eta$ 更新 $a,b$。$(a,b)=(1,1)$ 与 $(2,1/2)$ 的当前函数相同，但

$$
 a^+b^+
 =ab-\eta(abx-y)x(a^2+b^2)+O(\eta^2)
$$

中的 $a^2+b^2$ 不同。因此只取 $P(a,b)=ab$ 的摘要没有闭合训练合同；若训练合同要求精确预测下一步，就必须增加足以区分该方向的任务，例如优化器状态或梯度读出。

这不是说所有实现都必须保存 $a$ 与 $b$ 本身；规范最小商只保存任务族真正能够区分的部分。不同参数化若对同一合同诱导同一个闭合商，在合同内就是等价的。

### 推论 6.4（白盒性的工程判据）

要声称一个具体学习模型具有白盒接口，至少要公开并验证以下四项：

1. 状态摘要 $q$ 的实际定义；
2. 任务语言中允许的当前、未来、认证和更新读出；
3. 任务族在摘要纤维上的饱和性；
4. 每个允许动作在摘要上的下降映射。

只给出参数可视化、当前损失、单个 probe 或一个成功样本，最多验证任务族的一个子集，不能证明闭合。

## 7. 语义容量、取得费用与模型比较

### 定义 7.1（白盒资源向量）

对任务语言 $\mathcal T$ 和任务族 $\Gamma$，定义语义容量

$$
\sigma_\mathcal T(\Gamma)=|S/R_\Gamma|.
$$

给每个任务 $f$ 一个非负取得费用 $c(f)$，定义非自适应精确取得费用

$$
\mathsf C_\mathcal T(\Gamma)
=
\inf\left(\left\{
\sum_{f\in H}c(f):
H\subseteq\mathcal T,\ R_H\subseteq R_\Gamma
\text{，$H$ 有限}\right\}\cup\{+\infty\}\right),
\tag{7.1}
$$

其中只允许有限 $H$。若任务语言有限，或候选费用集合保证下确界达到，则可把 (7.1) 写成最小值；一般无限语言中不能省略 `inf`。自适应树的费用另记为 $\mathsf C^{\mathrm{ad}}$，因为它具有不同的控制合同。

### 命题 7.2（容量与取得费用不可互换）

不存在仅依赖 $\sigma_\mathcal T(\Gamma)$ 的函数，能够在所有有限任务语言上给出 $\mathsf C_\mathcal T(\Gamma)$；反之亦然。

**证明。** 取 $S$ 为四元素集。语言一包含一个费用为 $10$ 的单射任务；语言二包含两个费用各为 $1$ 的二值任务，其联合映射单射。两者的语义容量都是 $4$，但非自适应取得费用分别为 $10$ 与 $2$。反过来，取一个费用为 $1$ 的二值任务和一个费用为 $1$ 的四值单射任务，费用相同而语义容量分别为 $2$ 与 $4$。证毕。

所以比较白盒实现至少要保留一个向量，例如

$$
(\text{语义商大小},\ \text{任务取得费用},\ \text{更新闭包代价}),
$$

不能把参数量或一个平均指标当成全序质量分数。

### 定理 7.3（模型比较的闭合任务判据）

设两个有限确定性接口的可达状态集为 $S,S'$，允许任务语言为 $\mathcal T,\mathcal T'$，并有状态映射 $m:S\to S'$。设有任务语言之间的保持映射 $\Phi:\mathcal T\to\mathcal T'$，满足对每个 $f\in\mathcal T$ 存在 $\Phi(f)$ 使

$$
 f=\Phi(f)\circ m
$$

在可达状态上成立。若两侧有动作族 $U_a:S\to S$、$U'_a:S'\to S'$，并且 $m\circ U_a=U'_a\circ m$，同时 $\Phi$ 保持任务组合，则第一个实现对 $\mathcal T$ 的读数和动作结论可以运输到第二个实现。若某个 $f$ 不存在这样的 $\Phi(f)$，只能得到“该任务不能经由当前 $m$ 和 $\mathcal T'$ 表示”的接口不可表示结论；只有另行给出 $s,s'$ 或摘要纤维中的具体区分对时，才能称为状态逃逸见证。

**证明。** 对任务读出，下降等式直接给出相同结果；对任务组合和更新按假设归纳。若某个任务没有下降映射，定义上只说明目标接口没有提供该任务的表示，不推出某一对状态已经被区分；若再给出同一摘要纤维中的具体不同读数，才得到逃逸见证。证毕。

该定理的作用是限制“解释迁移”：两个网络的当前输出相同，不足以建立白盒等价；必须给出任务语言和动作的保持映射。

## 8. 仓内结果的参数对应与未决桥梁

本卷的抽象与当前项目结果有三条可核对的连接：

| 已有结果 | 在本卷中的位置 |
|---|---|
| [`FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md`](FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md) 的行为响应商和训练更新例 | 作为 $\Gamma_{\mathrm{learn}}$ 的具体任务源；本卷把它们放入任务—分割对偶，而不重算其数值表。 |
| `FIB_RELATIONAL_FIBER_CALCULUS.md` 的纤维饱和与运算下降判据 | 作为定理 2.2 和定理 6.2 的一般下降机制。 |
| `AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md` 关于相同平均通道和不同精确记录容量的结果 | 作为“任务语言不同则商不同”的记录层实例。 |

上述形式化来源给出一个具体的任务语言边界：proper 报告族的闭合不蕴含追加 continuation 后的 reply 族闭合。这个对应只支持“先固定任务语言，再谈白盒性”的方法论，不推出任何实际神经网络具有或不具有本卷的商。

仍未解决的桥梁是：对一个具体 FIB R2 递归实例，实际列出其完整任务语言，计算 $R_\Gamma$ 的闭包细化，并把最小非自适应探针覆盖与允许的自适应读数树分别算出。对真实神经网络，还必须取得可复现的状态摘要、动作接口和更新读出；普通参数检查或单次实验不能替代这些桥梁。

## 9. 研究结论和下一步

本卷的核心结论是

$$
\boxed{
\text{白盒性不是模型的固有标签，而是任务族与状态分割达到共同闭包固定点的性质。}
}
$$

由此可以把后续工作分成三个可检验的层次：

1. **语义层**：求任务族的规范商 $S/R_\Gamma$；
2. **取得层**：求分离逃逸对的最小覆盖或自适应决策树；
3. **动态层**：对动作和训练更新取未来闭包，检查摘要是否仍下降。

下一候选是一个具体有限 R2 实例：固定同一输入和失败任务族，构造其任务关系矩阵，求 $R_0,R_1,\ldots$，再以 (4.4) 计算 `101` 型关系探针和证书探针的最小覆盖。成功标准是得到一个同时包含关系、证书和更新三种任务的闭合分割；若所有新增任务都已由已有 future-response 商吸收，则记录该路线的吸收边界，而不把重述计作新结果。

## 追加锚（本行以下为增补区）
