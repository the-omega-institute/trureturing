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

## 10. 任意集合上的静态范围与条件化见证

### 定义 10.1（替代开篇与定义 1.1 的静态范围）

在通常含选择公理的集合论中，令 $S$ 为任意集合，$\mathcal T$ 为一组带有输出集的确定性任务 $f:S\to O_f$；$S$ 与 $O_f$ 均不要求有限。关系 $R_\Gamma$、任务族 $\mathcal T_R$、两侧闭包、规范商及逃逸对沿用 (1.1)、(1.2)、定义 1.3、2.1、4.1。第 1、2 节的静态结论与第 4 节的逻辑覆盖判据采用此范围，其精确陈述见定理 10.2、10.3。

动作仍为定义 3.1 的有限动作集及确定性全映射。定理 3.2、3.4 和 6.2 的关系恒等式与下降判据允许任意状态集；推论 3.3 的有限终止与严格细化次数上界仍要求 $S$ 有限。定义 7.1 的费用仍只在有限探针族上取下确界。定理 7.3 的有限接口假设保留，其运输范围由定理 10.7 指定。

### 定理 10.2（定理 1.2、1.4、2.2、2.3 的任意集合版本）

在定义 10.1 下，定理 1.2 的 Galois 等价、定理 1.4 的全部闭包律、定理 2.2 的读数因子分解及基数下界、定理 2.3 的规范满射与复合律均成立，不要求状态或输出有限。具体地，

$$
\Gamma\subseteq\mathcal T_R\iff R\subseteq R_\Gamma,
\qquad
R_{\mathcal T_{R_\Gamma}}=R_\Gamma,
\qquad
\mathcal T_{R_{\mathcal T_R}}=\mathcal T_R.
\tag{10.1}
$$

命题 2.4 在任意 $S$ 上的精确分离条件为

$$
\operatorname{cl}_{\mathrm{rel}}(R)=R
\iff
\forall s,s'\in S,\quad
s\not R s'\Longrightarrow
\exists f\in\mathcal T_R,\ f(s)\ne f(s').
\tag{10.2}
$$

特别地，若每个 $R$-类的指示函数都属于 $\mathcal T$，则此闭包等式成立。有限 $S$ 时，类指示函数可由单点指示函数作有限并得到，故保留命题 2.4 的有限情形；任意 $S$ 上不把有限单点组合自动视为所有类的指示函数。

**证明。** 定理 1.2 的证明逐项展开全称量词，没有使用有限性，故得到 (10.1) 的第一个等价。由 $\Gamma\subseteq\mathcal T_{R_\Gamma}$ 得 $R_{\mathcal T_{R_\Gamma}}\subseteq R_\Gamma$，反向包含由 $\mathcal T_{R_\Gamma}$ 的定义成立。对任意 $R$，有 $R\subseteq R_{\mathcal T_R}$，故 $\mathcal T_{R_{\mathcal T_R}}\subseteq\mathcal T_R$；而每个 $f\in\mathcal T_R$ 的核都包含 $R_{\mathcal T_R}$，给出反向包含。两种映射均反变，因而两侧闭包单调；以上等式又给出幂等性，包含自身的性质来自定义。这补全定理 1.4 在任意集合上的全部闭包律。

对 $q:S\to Q$，条件 $\ker q\subseteq R_\Gamma$ 恰使规则 $\bar f(q(s))=f(s)$ 在 $q(S)$ 上良定义；反向由因子分解立即成立。规则 $h(q(s))=[s]_{R_\Gamma}$ 同样良定义、唯一且满射，故有定理 2.2 的基数下界，且规范商达到该下界。定理 2.3 的代表元规则只用 $R_\Lambda\subseteq R_\Gamma$：它仍良定义、满射，恒等与复合律仍在每个代表元上成立。

最后，$R_{\mathcal T_R}$ 包含 $R$，而它排除一对 $(s,s')$ 当且仅当某个 $f\in\mathcal T_R$ 区分该对，这正是 (10.2)。类指示函数在 $R$ 上恒定并区分不同类，给出充分条件。

定义 10.1 所列动态判据的扩展也直接复用其原证明：定理 3.2 只用核的交集及有限动作词归纳，定理 3.4 只用任务并集对应核的交集，定理 6.2 只用读数和更新的良定义性；它们均未用状态有限。推论 3.3 的次数界则使用有限等价类计数，故该有限性条件保留。证毕。

### 定理 10.3（替代定理 4.2 的逻辑范围与取得条件）

令 $R_*\subseteq R_0$ 为任意集合 $S$ 上的等价关系。对任意任务族 $H\subseteq\mathcal T$，不论 $\mathcal P(R_0,R_*)$ 或 $H$ 是否有限，均有

$$
R_0\cap\bigcap_{f\in H}\ker f\subseteq R_*
\iff
\bigcup_{f\in H}C_f=\mathcal P(R_0,R_*).
\tag{10.3}
$$

此式本身不保证存在有限覆盖。若 $\mathcal P$ 有限且可被允许任务覆盖，则存在有限覆盖；若候选任务集 $F$ 有限且存在 $H\subseteq F$ 覆盖 $\mathcal P$，则非负实费用的最小总和在某个 $H$ 上达到。无限候选语言上，对满足 (10.3) 的有限 $H$，费用仍取 (7.1) 形式的下确界，未必达到；没有有限可行族时其值为 $+\infty$。

**证明。** 若右式成立，而 $(s,s')$ 属于左侧的交集却不属于 $R_*$，则 $\{s,s'\}\in\mathcal P$，应有某个 $f\in H$ 区分它，与该对属于 $\ker f$ 矛盾。反之，若覆盖失败，取未被覆盖的 $\{s,s'\}\in\mathcal P$；它属于 $R_0$ 及全部 $\ker f$，却不属于 $R_*$，故左式失败。这就是定理 4.2 的逐对证明，不使用有限性。

若有限 $\mathcal P$ 可覆盖，为每对选一个覆盖它的任务便得到有限子族。若 $F$ 有限且可行，有限幂集 $2^F$ 中的可行子族非空，故其费用集合有最小值。无限候选语言则不具备该有限最小值论证，故保留 (7.1) 的下确界形式。证毕。

### 命题 10.4（第 5 节的全实范围与推论 5.2 的替代陈述）

令状态集为 $S=\mathcal V=\mathbb R^\Sigma$，保留命题 5.1 的全部五点取值、实系数及实值求值任务；每个求值任务的像均为 $\mathbb R$。令 $R_0=R_{\Gamma_0}$，$R_*=\Delta_{\mathcal V}$ 为恒等关系，$g=\operatorname{ev}_{101}$。则

$$
C_g=\mathcal P(R_0,\Delta_{\mathcal V}),
\qquad
R_0\cap\ker g=\Delta_{\mathcal V},
\tag{10.4}
$$

其中逃逸对集合无限。命题 5.1 的每个训练纤维仍恰为一条仿射直线 $f+\mathbb R h$；(10.4) 是定理 10.3 的单任务全覆盖实例。

记四点读数为 $E_0:\mathcal V\to\mathbb R^4$。推论 5.2 中只依赖这些读数的摘要具体指 $q=\psi\circ E_0$。对这样的 $q$，$g$ 不能经 $q$ 下降。若未来任务 $t$ 满足某个 $f\in\mathcal V$、$\lambda\ne0$ 上 $t(f+\lambda h)\ne t(f)$，则这两个状态同样给出 $t$ 的逃逸见证；这不要求 $t$ 覆盖全部逃逸对。

**证明。** 直接使用命题 5.1 已有的核计算：$fR_0f'$ 当且仅当 $f'-f=\lambda h$。若 $f\ne f'$，则 $\lambda\ne0$，而 $g(f')-g(f)=\lambda$，故每个逃逸对都被 $g$ 覆盖，得到 (10.4)。令 $0$ 为零函数，映射

$$
\mathbb R\setminus\{0\}\longrightarrow\mathcal P(R_0,\Delta_{\mathcal V}),
\qquad
\lambda\longmapsto\{0,\lambda h\}
$$

是单射，故逃逸对集合无限。常值函数 $f\equiv c$ 在任一点的求值为 $c$，故每个求值任务的像均为 $\mathbb R$。仿射纤维结论仍来自同一核计算，没有改变命题 5.1 的线性代数。

对 $q=\psi\circ E_0$，有 $q(f+\lambda h)=q(f)$；若 $g$ 或上述 $t$ 能经 $q$ 下降，它们就应在该对上相同，矛盾。若另要求 $q$ 准确支持全部 $\Gamma_0$ 读数，则 $\ker q=R_0$；仅有“支持 $\Gamma_0$”的条件 $\ker q\subseteq R_0$ 不排除摘要保留额外信息。这里 $\dim_{\mathbb R}\mathcal V=5$ 与纤维维数 $1$ 均为维数陈述，不是有限状态数陈述；定理 10.3 的应用不使用逃逸对的有限枚举或推论 3.3 的有限终止。证毕。

### 命题 10.5（替代例 6.3 的非退化训练见证）

对固定实数 $x,y,\eta$，把例 6.3 的更新明确为平方损失的同步梯度步。记 $e=abx-y$，则

$$
U_{x,y,\eta}(a,b)=(a-\eta ebx,\ b-\eta eax),
\qquad
q(a,b)=ab.
$$

两个同摘要状态 $(1,1)$ 与 $(2,1/2)$ 经此步后摘要不同，当且仅当

$$
\eta x(x-y)\ne0.
\tag{10.5}
$$

若允许的训练动作包含满足 (10.5) 的一步，则 $q$ 不满足定理 6.2 的更新合同，亦不能精确读出该步后的乘积预测。

**证明。** 精确展开而非截断得

$$
q(U_{x,y,\eta}(a,b))
=ab-\eta ex(a^2+b^2)+\eta^2e^2abx^2.
$$

在上述两点均有 $ab=1$、$e=x-y$，二次项相等，而 $a^2+b^2$ 分别为 $2$ 与 $17/4$，故

$$
q(U_{x,y,\eta}(2,1/2))-q(U_{x,y,\eta}(1,1))
=-\frac94\eta x(x-y).
\tag{10.6}
$$

于是 (10.5) 正是此对的分离条件。它成立时，同一 $q$ 值产生两个后继 $q$ 值，故更新不能经 $q$ 下降。例如 $x=1,y=0,\eta\ne0$ 满足此条件。条件失败时，此对不提供不闭合见证；不能由此断言整个训练合同闭合。证毕。

### 命题 10.6（命题 4.4 的全局与相对冗余含义）

命题 4.4 的 (4.5) 是全局冗余判据：加入 $f$ 不改变 $R_\Gamma$，当且仅当 $R_\Gamma\subseteq\ker f$。若另给当前等价关系 $R$，相对冗余定义为加入 $f$ 不改变 $E=R\cap R_\Gamma$，其判据为

$$
R\cap R_\Gamma\subseteq\ker f.
\tag{10.7}
$$

任一判据失败时，取相应关系内被 $f$ 区分的一对，便得到严格细化见证。

**证明。** 全局情形引用命题 4.4。相对情形中加入 $f$ 后的关系为 $E\cap\ker f$；它等于 $E$ 当且仅当 $E\subseteq\ker f$，否则恰删去被 $f$ 区分的关系对。证毕。

### 定理 10.7（定理 7.3 的像内运输与带类型组合）

保留定理 7.3 的有限状态集、确定性动作及映射 $m:S\to S'$。对每个 $f\in\mathcal T$，使 $\Phi(f)$ 取值于同一输出集，并假设

$$
f=\Phi(f)\circ m,
\qquad
m\circ U_a=U'_a\circ m.
$$

则 $m(S)$ 对全部 $U'_a$ 稳定；对每个有限动作词 $\alpha$ 和每个 $s\in S$，

$$
m(U_\alpha(s))=U'_\alpha(m(s)),
\qquad
f(U_\alpha(s))=\Phi(f)(U'_\alpha(m(s))).
\tag{10.8}
$$

对两侧任务语言允许的有限联合及输出后复合，“保持任务组合”的像内含义明确为：若 $f_i:S\to O_i$、$v:\prod_{i=1}^kO_i\to O$，且 $t=v\circ\langle f_1,\ldots,f_k\rangle\in\mathcal T$，则

$$
\left.\Phi(t)\right|_{m(S)}
=\left.(v\circ\langle\Phi(f_1),\ldots,\Phi(f_k)\rangle)\right|_{m(S)}.
\tag{10.9}
$$

上述运输只断言像内匹配读数及匹配动作。若另有 $m(S)=S'$，才覆盖全部目标状态；即使如此，结论也只涉及已匹配的任务，不包含其他目标任务、取得费用或最优值的保持。

**证明。** 单步交换式给出 $U'_a(m(s))=m(U_a(s))\in m(S)$，故像稳定。从空词的恒等映射开始，按动作词长度归纳得到 (10.8) 的第一个式子；对 $U_\alpha(s)$ 应用读数等式得到第二个。对 $y=m(s)$，有

$$
\Phi(t)(y)=t(s)
=v(f_1(s),\ldots,f_k(s))
=v(\Phi(f_1)(y),\ldots,\Phi(f_k)(y)),
$$

故 (10.9) 在像上成立；要求此式在像外成立须另加相应假设。所有证明只在形如 $m(s)$ 的状态上取值，故不约束 $S'\setminus m(S)$；当 $m$ 满射时这些状态为空。假设没有指定其他目标任务的匹配或费用关系，因而不提供这些结论。证毕。

## 追加锚（本行以下为增补区）
## 11. 初始化根纤维、逃逸冲突与因果白盒状态

> 本增补把初始化根纤维分析接入任务—分割卷：它研究在有限、确定性、部分可行的观察协议中，隐藏历史是否已在寄存器初始化时被同一初值合并。它不修改 [Fibonacci 原子关系生成卷](FIBONACCI_ATOMIC_RELATION_GENERATION.md)，也不把 Boundary Dynamics continuation §116 的中点冲突团簇搬到更早的边界。现有的无根 promise-coloring 与 DFAO 等价、任务—分割商和逃逸探针覆盖分别见 [`PromiseColoringTotalization`](../../../D5/S0/Automata/PromiseColoringTotalization.lean) 与本卷前文。
>
> `PromiseColoringTotalization` 的相关构造只有一个可见空词起点 `start := c.color(root seed)`；它不允许每个前缀类独立选择起始颜色。本增补所区分的是多个隐藏 occurrence 根共享一个空的可见轨迹，和该来源的单一可见前缀根。全文只作声明的有限模型内的数学推导，不声称真实神经网络满足这些前提，也不把普通 Markdown 文字当作 Lean 真值；机器学习段落的验证边界仍是纸面上的协议推理。

### 11.0 范围与差分

#### 11.0.1 模型边界

本增补固定以下合同：

有限参数化本身不推出 occurrence forest：参数可以在不同历史时刻重访同一状态。凡使用根冲突结论，协议域必须另外声明一个有限的、带 occurrence 标签的许可历史域，或一个满足同样协议假设的有限 history unfolding；底层参数化与 occurrence identity 分开记录。

- 隐藏历史是有限的 occurrence forest 节点；每个节点带有从某个初始化根开始的唯一公开事件词；
- 公开事件来自有限字母表，每个事件在每个历史上有确定的部分后继；
- 终端记录和目标值是有限、确定且由接收端可见的；
- 寄存器在根边界只有一个固定初值，或者由一个明确的初始标签通道给出标签；
- 所有需要实现的历史、事件词和终端记录都属于同一个声明的合法域。

“部分”只表示某个事件在某个隐藏历史上不合法。若一个事件只在一侧合法，协议是否要求接收端响应该非法分支，必须在合同中单独声明；本增补的冲突只使用双方都合法的公共继续。

#### 11.0.2 新增层与复用层

| 内容 | 状态 | 本增补作用 |
| --- | --- | --- |
| 有限自动机的稳定着色、公共继续冲突和状态预算 | `repo-derived`，见 `D5/S0/Automata/PromiseColoringTotalization.lean` | 复用无根的动态着色核心 |
| 任务族诱导的规范商和逃逸对覆盖 | `repo-derived`，见 `FIB_TASK_PARTITION_GALOIS_AND_WHITEBOX.md` | 复用任务依赖的状态判据 |
| 根纤维冲突导致的固定初始化不可行、自由初始标签的精确色数、切面移动的合同边界 | 本增补新增的有限模型综合 | 说明“增加后续记忆”与“在更早处保留区别”不是同一资源 |
| Boundary Dynamics continuation §116 的中点冲突团簇 | 既有结果的参数对应 | 作为取得种子之后的下界，不被改写成预种子根冲突 |

本增补不把无根着色—自动机等价重新申领为新一般理论。它只增加根集合、初始标签和边界移动三个参数。

### 11.1 有根的有限观察协议

#### 定义 11.1.1（根 occurrence forest）

一个有限有根协议记为

$$
\mathcal P=(H,H_\circ,E,\delta,\ell,R,\operatorname{Term},t),
$$

其中：

- $H$ 是非空有限隐藏历史集，$H_\circ\subseteq H$ 是非空根集；
- $E$ 是有限公开事件字母表；
- 对每个 $e\in E$，$\delta_e:H\rightharpoonup H$ 是确定的部分后继；
- $\ell:H\to E^*$ 是公开事件词，根满足 $\ell(h)=\varepsilon$，且若 $\delta_e(h)=h'$，则 $\ell(h')=\ell(h)e$；
- $R$ 是非空有限终端记录集；
- $\operatorname{Term}\subseteq H\times R$ 是合法终端对；
- $t:\operatorname{Term}\to Y$ 给出目标值，其中 $Y$ 是非空集合。

对根 $h_\circ\in H_\circ$，令

$$
\operatorname{Reach}_\delta(h_\circ)=\{\delta_w(h_\circ):w\in E^*,\ \delta_w(h_\circ)\text{ 定义}\}.
$$

要求

$$
H=\bigcup_{h_\circ\in H_\circ}\operatorname{Reach}_\delta(h_\circ),
$$

且不同根的 occurrence trees 不相交：若 $h_\circ\ne h'_\circ$，则

$$
\operatorname{Reach}_\delta(h_\circ)\cap\operatorname{Reach}_\delta(h'_\circ)=\varnothing.
$$

在同一棵树中，给定公开事件词至多有一个节点。因而每个节点有唯一根归属，$H$ 中没有未由声明的转移从根实际到达的幽灵节点；$\ell$ 只记录公开轨迹，不把隐藏根身份偷偷加入接收端输入。

对词 $w=e_1\cdots e_k$，令 $\delta_w$ 为按顺序复合的部分后继，空词的后继为恒等。

#### 定义 11.1.2（公共继续与逃逸冲突图）

若 $h,h'\in H$，称 $(w,r)$ 是它们的公共合法终端继续，当且仅当

$$
\delta_w(h),\delta_w(h')\text{ 都定义},
$$

且

$$
(\delta_w(h),r),(\delta_w(h'),r)\in\operatorname{Term}.
$$

称 $h,h'$ 构成逃逸冲突，当存在公共合法终端继续 $(w,r)$ 使

$$
 t(\delta_w(h),r)\ne t(\delta_w(h'),r).
$$

由此得到简单图 $G_{\mathcal P}$：顶点是 $H$，边正是逃逸冲突。根冲突图为诱导子图

$$
G_\circ=G_{\mathcal P}[H_\circ].
$$

冲突使用完整公开事件词和相同终端记录；只比较当前输出，或只比较部分事件前缀，都不能替代这个定义。

#### 定义 11.1.3（稳定着色）

给定有限颜色集 $C$，映射 $c:H\to C$ 称为稳定着色，如果满足：

1. **根条件：** 存在 $c_\circ\in C$，使 $c(h)=c_\circ$ 对所有 $h\in H_\circ$ 成立；
2. **后继条件：** 若 $c(h)=c(h')$，且 $\delta_e(h),\delta_e(h')$ 都定义，则
   $$
   c(\delta_e(h))=c(\delta_e(h'));
   $$
3. **终端条件：** 若 $c(h)=c(h')$，且 $(h,r),(h',r)\in\operatorname{Term}$，则
   $$
   t(h,r)=t(h',r).
   $$

记

$$
\chi_\circ(\mathcal P)
=
\min\{|c(H)|:c\text{ 是稳定着色}\},
$$

若不存在稳定着色，则约定 $\chi_\circ(\mathcal P)=+\infty$。

由后继条件逐步归纳，稳定着色自动是冲突图的 proper coloring：若 $c(h)=c(h')$，则公共继续上的后继颜色相同，再由终端条件得到相同目标。

#### 定义 11.1.4（固定初始化的 blind 实现）

固定初始化的 blind 实现是有限非空状态集 $Q$、固定初态 $q_0\in Q$、全转移表

$$
\bar\delta:Q\times E\to Q
$$

和终端解码器

$$
D:Q\times R\to Y,
$$

使得从任意根开始都以 $q_0$ 启动，并且沿合法公开词运行时，对每个 $(h,r)\in\operatorname{Term}$ 都满足

$$
D(q(h),r)=t(h,r),
$$

其中 $q(h)$ 是沿 $\ell(h)$ 从 $q_0$ 运行得到的状态。定义实际可达状态集

$$
Q_{\mathrm{reach}}=\{q(h):h\in H\}.
$$

状态成本只计 $|Q_{\mathrm{reach}}|$；全转移表为未到达的颜色—事件组合添加的默认状态不计入最小状态数，也不承担任务结果。$Y\ne\varnothing$ 保证默认终端输出可以选取。

定义固定初始化的最小实际状态数为

$$
D_{\mathrm{fixed}}(\mathcal P)=
\min\{ |Q_{\mathrm{reach}}|:\text{存在定义 11.1.4 的准确实现 }(Q,q_0,\bar\delta,D)\},
$$

若实现集合为空则约定该最小值为 $+\infty$。

### 11.2 根冲突是先于容量的不可行性

#### 定理 11.2.1（根冲突阻断固定初始化）

若 $\mathcal P$ 存在固定初始化的 blind 实现，则

$$
G_\circ\text{ 无边}.
$$

因此，只要存在两个根历史 $h,h'\in H_\circ$ 和公共合法终端继续 $(w,r)$，满足

$$
 t(\delta_w(h),r)\ne t(\delta_w(h'),r),
$$

则任何有限的后续状态数都不能实现该合同：增加寄存器容量不会恢复在根边界已经被合并的区别。

##### 证明

两个根从同一个 $q_0$ 启动。由于转移表确定，沿相同公开词 $w$ 后到达同一个寄存器状态 $q_w$。终端记录也相同，故解码器给出同一个

$$
D(q_w,r).
$$

这不可能同时等于两个不同目标。故根冲突边不存在。∎

#### 定理 11.2.2（根无冲突时的有限可行性）

在定义 11.1.1 的 occurrence-forest 假设下，若 $G_\circ$ 无边，则存在固定初始化的有限 blind 实现。因此：

$$
\boxed{
\text{固定初始化可行}
\quad\Longleftrightarrow\quad
G_\circ\text{ 无边}.
}
$$

##### 证明

给每个节点使用其公开词作为颜色：

$$
 c_{\mathrm{trace}}(h)=\ell(h).
$$

根都得到空词颜色，满足根条件；后继条件由

$$
\ell(\delta_e(h))=\ell(h)e
$$

直接得到。

只需验证终端条件。若两个节点 $h,h'$ 有相同公开词 $w$、同一终端记录 $r$，且目标不同，则它们分别来自两个根的同一公共继续 $w$，从而根之间有冲突边；这与 $G_\circ$ 无边矛盾。若它们来自同一根，则 occurrence-forest 的唯一性给出 $h=h'$。所以终端条件成立。

$H$ 有限，公开词颜色只有有限多个。由推论 11.2.3 的构造，用颜色作为寄存器状态：若某颜色—事件组合存在代表节点，则取其后继颜色；若不存在则取任意默认颜色。后继条件保证取值与代表无关。终端解码器在每个有代表的颜色—记录对上取目标值；终端条件保证良定义，其余对取固定默认值。沿公开词归纳，寄存器状态等于 $c_{\mathrm{trace}}$，于是得到准确实现。∎

定理 11.2.2 的充分性依赖三个词：**根集是同一初始化边界、冲突量词包含全部公共继续、节点是 occurrence history**。删去任一词，结论都可能变成错误的有限状态断言。

#### 推论 11.2.3（固定初始化的精确状态数）

在 $G_\circ$ 无边时，固定初始化 blind 实现的最小状态数为

$$
\boxed{
D_{\mathrm{fixed}}(\mathcal P)=\chi_\circ(\mathcal P).
}
$$

若 $G_\circ$ 有边，则

$$
\boxed{
D_{\mathrm{fixed}}(\mathcal P)=+\infty.
}
$$

##### 证明

任意实现把每个 occurrence history 映射到其实际寄存器状态，得到满足三条稳定条件的着色，故状态数给出下界。反向方向由稳定着色定义转移和解码器：对每个颜色 $q$ 和事件 $e$，若存在 $h$ 使 $c(h)=q$ 且 $\delta_e(h)$ 定义，就令

$$
\bar\delta(q,e)=c(\delta_e(h));
$$

后继条件使其与代表 $h$ 无关；没有代表时使用固定默认颜色。若存在 $h$ 使 $c(h)=q$ 且 $(h,r)\in\operatorname{Term}$，令

$$
D(q,r)=t(h,r);
$$

终端条件使其良定义，未出现的对取默认值。沿 occurrence tree 归纳即可。∎

这个最小值与 `PromiseColoringTotalization` 所处理的无根设置的差别在于初始化边界：该构造只有一个可见前缀根，并从一个空词起点 `start := c.color(root seed)` 开始；它不让每个前缀类各自选择独立的起始颜色。这里的根冲突来自多个隐藏 occurrence 根共享同一个空的可见轨迹。固定初始化把这些根历史压进同一个颜色；根边存在时，区别不是“需要更多颜色”，而是“该合同没有有限实现”。

### 11.3 初始标签是独立于总记忆的资源

#### 定义 11.3.1（初始标签通道）

初始标签通道是一个映射，其中 $I$ 是非空有限标签集：

$$
\iota:H_\circ\to I,
$$

它在任何公开事件发生前为根历史提供一个标签。这里的标签预算按可区分的初始寄存器状态计数：给定一个有限的初始化状态载体 $Q_0$，标签写入包含一个注入

$$
\jmath:I\hookrightarrow Q_0,
$$

实际初态映射为 $\jmath\circ\iota:H_\circ\to Q_0$；也可以直接把 $I$ 识别为这些初始状态。标签可以直接写入寄存器初值；本节的“自由”指 $\iota$ 可以按隐藏根历史指定，不声称它已经能由公开观察计算出来。若标签不能在根边界取得，必须把其生成过程并入协议，不能把 $|I|$ 当作免费容量。

根图的色数记为

$$
\iota_\circ(\mathcal P)=\chi(G_\circ),
$$

其中 $H_\circ\ne\varnothing$，所以色数至少为 $1$。

#### 定理 11.3.2（初始标签复杂度的精确阈值）

在自由初始标签模型中：

1. 任何正确实现的初始标签映射都满足
   $$
   |I|\ge\chi(G_\circ);
   $$
2. 若 $|I|\ge\chi(G_\circ)$，则可以选择一个 proper 根标签，并构造有限确定性实现。

因此，

$$
\boxed{
\text{使初始化不再产生不可行根合并所需的最少标签数}
=
\chi(G_\circ).
}
$$

##### 证明

若根冲突边连接 $h,h'$，它们必须获得不同的初始寄存器状态；否则定理 11.2.1 的相同继续论证仍然成立。因此任何初始标签是 $G_\circ$ 的 proper coloring，给出第一项。

反过来，取一个用 $|I|$ 个标签实现的 proper coloring。把状态写成 $(i,w)$，其中 $i$ 是初始标签，$w$ 是已见公开词；只保留有限协议中实际出现的二元组，并为未到达组合添加默认状态。事件转移为

$$
(i,w)\longmapsto(i,we).
$$

若同一 $(i,w)$ 对同一终端记录 $r$ 出现两个不同目标，则相应根历史具有同一初始标签、同一公开词和同一终端记录，因而构成根冲突边，和标签 proper 矛盾。于是终端解码器良定义。状态集有限，且实现所有合法终端结果。∎

#### 推论 11.3.3（容量与初始化的三种状态）

固定初始化、自由初始标签和完整历史记忆是三个不同资源合同：

$$
\begin{array}{c|c}
\text{合同}&\text{根层结论}\\ \hline
\text{固定一个初值}&G_\circ\text{ 必须无边}\\
\text{可取得初始标签}&|I|\ge\chi(G_\circ)\\
\text{把根历史直接放入状态}&|H_\circ|\text{ 个标签总能实现}
\end{array}
$$

第三行只是有限域中的显然上界，不等于取得这些标签没有成本。初始标签若必须由公开端口、训练数据或合法事件生成，则应把生成过程并入协议；不能把自由指定的 $\iota$ 当作免费白盒读数。

#### 反例 11.3.4（无根着色存在而固定初始化不可能）

令根集为 $H_\circ=\{u,v\}$。只有一个公开事件 $e$，且

$$
\delta_e(u)=s_0,\qquad \delta_e(v)=s_1.
$$

令同一个终端记录 $r$ 在 $s_0,s_1$ 上都合法，但

$$
 t(s_0,r)=0,\qquad t(s_1,r)=1.
$$

不加共同根初始化条件时，给 $u,s_0$ 颜色 $0$，给 $v,s_1$ 颜色 $1$，得到一个两色稳定着色；这只说明去掉共同初始化边界后的着色存在，并不是“每个前缀类各自选择起点”的结论。可是根图含有边 $uv$，固定初值要求 $u,v$ 同色，定理 11.2.1 说明不存在任何固定初始化实现。

给根提供一位初始标签后，取 $\iota(u)=0,\iota(v)=1$，两色实现立即可得。这里初始标签把不可行性变成了有限资源问题；后续寄存器扩容本身做不到这一点。

### 11.4 读通道的单调性必须保持协议

#### 定义 11.4.1（被动读通道扩展）

称 $\mathcal P'$ 是 $\mathcal P$ 的被动读通道扩展，如果：

1. 隐藏历史、根集、事件词、合法后继、终端记录和目标完全相同；
2. 每个事件额外提供一个有限读字母表 $K$ 中的值 $\kappa$ 给寄存器更新器；
3. 原协议的更新器可以忽略 $\kappa$，且读通道不消耗一次性来源、不改变合法域、不改变终端解码合同。

在这里，$D_{\mathrm{blind}}(\mathcal P)$ 定义为定义 11.1.4 的最小实际可达状态数；$D_{\mathrm{read}}(\mathcal P')$ 定义为允许更新器使用每步被动读值的有限表

$$
\bar\delta_{\mathrm{read}}:Q\times E\times K\to Q,
$$

并沿实际的配对事件—读值轨迹运行、仍使用单一初态和同一终端解码合同的相应最小实际可达状态数。两者都只计合法历史实际到达的状态。

#### 命题 11.4.2（被动扩展的容量单调性）

在被动读通道扩展下，

$$
D_{\mathrm{read}}(\mathcal P')
\le
D_{\mathrm{blind}}(\mathcal P).
$$

##### 证明

把任意 blind 更新器视为读通道更新器，令其忽略 $\kappa$。根初值、公开事件、合法终端和解码器全部保持不变，所以原实现仍然正确。对所有实现取最小值得到不等式。∎

若读通道改变合法转移、消耗来源、增加或删除终端记录、改变选择器，$\mathcal P'$ 与 $\mathcal P$ 已不是同一个合同；此时不能从“多了一个读值”推出上述不等式。比较必须先重新构造各自的冲突图和根集。这里 $D_{\mathrm{blind}}$ 与 $D_{\mathrm{read}}$ 分别表示这两个合同下按实际可达状态计的最小值。

### 11.5 切面迁移：重新生根改变初始化合同

#### 定义 11.5.1（Occurrence forest 的切面与两种合同）

在祖先关系

$$
h\preceq h'\quad\Longleftrightarrow\quad h'=\delta_w(h)\text{ 对某个 }w\in E^*\text{ 定义}
$$

下，取一个非空有限 antichain $C\subseteq H$，即 $C$ 中任意两个节点互不为祖先。令

$$
H_C=\bigcup_{c\in C}\operatorname{Reach}_\delta(c),
\qquad
\operatorname{Term}_C=\operatorname{Term}\cap(H_C\times R),
$$

并把每个 $c$ 视为后续协议的根；对 $H_C$ 中从 $c$ 到达的节点 $h$，将原公开词重置为唯一的后缀词 $\ell_C(h)$，满足

$$
\ell(h)=\ell(c)\,\ell_C(h),\qquad \ell_C(c)=\varepsilon.
$$

后继限制为 $H_C$ 上的原有 $\delta_e$，终端记录限制为 $\operatorname{Term}_C$。这等价于只研究那些在该切面之后仍有合法后续的路径；所得、以 $C$ 为根的后缀协议记为

$$
\mathcal P\!\upharpoonright_C.
$$

在这个切面上区分两种初始化合同：

- **重置合同**把所有 $c\in C$ 送入同一个固定初值；
- **携带合同**给每个 $c$ 一个切面状态 $\sigma(c)$，其中 $\sigma$ 必须是切面之前某个实际实现沿合法前缀运行得到的状态映射。

令 $G_C$ 表示 $\mathcal P\!\upharpoonright_C$ 的根冲突图。这里的根是切面节点 $C$，冲突只量化切面之后的公共合法继续。切面节点被重新称为“根”并不表示它们已经能够从原协议的固定初值取得。

#### 定理 11.5.2（切面合同迁移定理）

对任意上述切面 $C$：

1. 重置合同存在有限准确实现，当且仅当 $G_C$ 无边；在可行时，其最少持久状态数是切面协议的稳定着色数。
2. 若切面标签可以自由按 $c\in C$ 指定，则避免根层合并所需的最少标签数是
   $$
   \chi(G_C).
   $$
3. 若原协议已有固定初始化实现，且 $\sigma(c)$ 是该实现到达 $c$ 时的实际状态，则携带合同沿用该实现而可行；这只是把已经支付的前缀状态带过切面。
4. $G_C$ 的一个 proper coloring 单独只能证明切面之后的自由标签或重置问题；它不能反推出原协议从其更早固定初值可实现。后者仍须满足原根图 $G_\circ$ 无边。

##### 证明

前两项把定理 11.2.1、定理 11.2.2 和定理 11.3.2 应用于后缀协议 $\mathcal P\!\upharpoonright_C$。第三项沿原实现的运行归纳：切面状态由 $\sigma$ 给出，之后每个事件使用原转移，终端使用原解码器。第四项来自初始化合同不同：切面 coloring 没有提供从旧根到 $C$ 的生成映射；若旧根存在公共继续冲突，定理 11.2.1 仍给出不可行性。∎

#### 推论 11.5.3（Boundary Dynamics continuation §116 的正确接法）

[Boundary Dynamics continuation](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS_CONTINUATION.md) §116 的 Proposition 116.8 与 Theorem 116.9 已在其原合同中给出：固定种子 $\rho=\theta$、完成前半段标记并到达中点后，有

$$
W=\binom a{a/2}
$$

个中点历史由公共后续区分，并因此满足该卷所定义的

$$
W\le D_{\mathrm{blind}}(\pi_k).
$$

本增补只作切面参数对应，不重证这两个已有结果。它们属于**取得种子之后的中点切面**：寄存器已经从固定初值运行过种子取得和原始解析事件，中点历史是切面节点，而不是预种子根。

若把同一批中点节点改称为初始化根，就已经改用了重置或自由标签合同；若把切面状态沿用，则使用的是携带合同。两者都不能把 $W$ 自动变成预种子根图的团或预种子容量公式。预种子边界必须另行计算 $G_\circ$；若该图有边，定理 11.2.1 给出的是固定初始化不可行，而不是有限的 $W$ 下界。

因此对 §116 的资源记账应写成

$$
\boxed{
(\text{预种子初始通道},\ \text{中点持久状态下界 }W,\ \text{终端响应种类数})
}
$$

三项分别属于不同切面合同。已有 Boundary Dynamics continuation §115.3 的

$$
D_{\mathrm{read}}=D_{\mathrm{blind}}=2<H_{\mathrm{resp}}=3
$$

还说明响应函数数量与寄存器最小值是不同的优化问题。

### 11.6 机器学习白盒性的初始化逃逸证书

#### 定义 11.6.1（学习合同的根纤维）

令 $\Theta$ 是有限的底层隐藏参数化集，$\Theta_\circ\subseteq\Theta$ 是非空、在模型进入训练、干预或推理协议之前已经存在的根参数化集。另给一个有限的许可 occurrence-labelled 历史域 $H_{\mathrm{ML}}$、根集 $H_{\circ,\mathrm{ML}}$ 以及投影 $p:H_{\mathrm{ML}}\to\Theta$，其中 $p(H_{\circ,\mathrm{ML}})\subseteq\Theta_\circ$；不同 occurrence 可以投影到同一个参数状态。要求 $H_{\mathrm{ML}}$ 及其许可转移满足定义 11.1.1 的可达性、根树不相交和唯一公开词条件，或显式给出一个满足这些条件的有限 history unfolding。有限的 $\Theta$ 只保证底层参数种类有限，不替代这个 occurrence 域假设。

$q_0$ 是实际接口使用的固定初始摘要，并对应 $H_{\circ,\mathrm{ML}}$ 的共同根状态。允许动作形成有限公开事件词，训练或认证目标作为终端记录后的目标值。由这些数据得到有限协议

$$
\mathcal P_\mathrm{ML}=(H_{\mathrm{ML}},H_{\circ,\mathrm{ML}},E,\delta,\ell,R,\operatorname{Term},t).
$$

如果两个根 occurrence $h,h'\in H_{\circ,\mathrm{ML}}$ 具有相同的固定初始摘要，却存在相同的合法动作/读数词和相同的终端记录，且目标不同，则称为**初始化逃逸证书**；其底层参数 $p(h),p(h')$ 可以相同或不同。

#### 定理 11.6.2（初始化逃逸阻断白盒实现）

在有限确定性学习合同中，初始化逃逸证书排除任何从共同初始摘要出发的精确有限状态白盒接口。只有增加一个在该根边界可取得的区分通道，或改变任务合同使该继续不再同时合法，才可能恢复可行性。

##### 证明

这是定理 11.2.1 应用于 $\mathcal P_\mathrm{ML}$。共同初始摘要给出同一寄存器初态；相同动作/读数词和终端记录给出同一解码输入，而证书要求两个不同目标，矛盾。后续增加状态只改变共同轨迹上的状态集合，不能改变确定性寄存器在同一输入词上的唯一运行。∎

#### 推论 11.6.3（当前输出相同不等于白盒等价）

两个模型可能满足

$$
P(\theta)=P(\theta')
$$

而在相同训练动作后给出不同优化器读出、认证结果或下一步目标。若这两个参数化在初始化时已被压到同一个摘要，并且该差异由一个共同合法继续见证，则当前预测的相等只说明一个任务核相等，不能说明学习合同下的状态可合并。

这把“白盒性”的失败分成两类：

- **容量失败：** 根边界已经可区分，但后续摘要没有保留足够状态；
- **初始化失败：** 根边界把存在公共未来差异的历史直接合并，任何后续容量都无法修复。

两者需要不同的修复：前者增加或重编码持久状态，后者增加更早的读数或改变初始化合同。

### 11.7 统一的根—状态—响应谱

#### 定义 11.7.1（三种容量）

对任意有限协议，定义：

- $D_{\mathrm{root}}=\chi(G_\circ)$：自由初始标签的最少数量；
- $D_{\mathrm{fixed}}=\chi_\circ(\mathcal P)$：固定初值下的最少实际可达持久状态数，若不可行则为 $+\infty$。

对于 [Boundary Dynamics continuation](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS_CONTINUATION.md) §115 的特定实例，另按 §115.3 的 displayed definition 记

$$
H_{\mathrm{resp}}(\pi^-)=\max(\{1,D\}\cup\{|\{g_u:u\in W_b\}|:\rho\in\{0,1\},\ c<58,\ N_b>0\}).
$$

它统计指定 bare boundary 上不同完整未来响应函数的最大数量；本增补不把这个 §115 特定量泛化为任意协议的定义。

#### 定理 11.7.2（根—状态—响应的不可混同）

对任意有限协议，前两项满足

$$
\boxed{
\omega(G_\circ)\le D_{\mathrm{root}},
\qquad
D_{\mathrm{fixed}}<\infty\Longleftrightarrow G_\circ\text{ 无边}.
}
$$

在 Boundary Dynamics continuation §115 的特定固定初始化 blind 合同中，§115.3 另给出严格分离

$$
D_{\mathrm{blind}}=2<H_{\mathrm{resp}}(\pi^-)=3.
$$

所以该实例中完整未来响应函数的数量不能替代寄存器最小值；这不是对任意协议重新定义一个 $H_{\mathrm{resp}}$。

##### 证明

第一项是有限图的团数不超过色数，第二项是定理 11.2.1 和 2.2。§115 的严格不等式是其自身实例的既有结论；它比较的是该实例的 blind 寄存器合同与 §115.3 的响应函数计数，不能被推广成任意协议的统一等式。∎

#### 推论 11.7.3（边界移动不是免费重参数化）

若两个实现只在观察切面位置不同，则必须同时比较：

1. 根集合和固定初值；
2. 切面之前可见的事件词；
3. 切面之后的合法继续和终端记录；
4. 哪些读值进入寄存器更新；
5. 哪些值进入最终解码器。

只把同一组中点历史重新命名为“初始状态”，不能证明两个实现的容量相同，也不能把一个切面上的有限下界移植到另一个切面。

### 11.8 结果边界与后续可检验问题

本增补已经在声明的有限 occurrence-forest 模型内给出四个可复用结论：根冲突是固定初始化的不可行性证书；自由初始标签的精确阈值是根冲突图色数；被动读通道的单调性需要保持合法协议与终端合同；切面上的重置、自由标签和携带状态属于不同初始化合同，切面 coloring 不能回溯证明更早固定初值可行。

尚未由此推出：连续或随机模型中的同一结论、带噪初始通道的概率界、神经网络训练的经验性白盒率、任意 FIB 实例的预种子根图，或 $H_{\mathrm{resp}}$ 与总控制/时间/能量成本的等价。

下一项具体候选是：选定一个已有 FIB R2 实例，固定预种子、种子取得、中点和终端四个切面，分别列出四个根图和公共继续矩阵；若同一实例在不同切面上出现“有限容量—根不可行—有限容量”的三段谱，则把它作为切面移动的实例定理，而不是把中点团簇外推成预种子结论。

## 追加锚（本行以下为增补区）
