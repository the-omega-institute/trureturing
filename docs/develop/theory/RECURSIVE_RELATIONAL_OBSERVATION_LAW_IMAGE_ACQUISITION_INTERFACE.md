# Recursive relational observation: semantic law-image and acquired boundary

本卷增加一个接口层：区分完整模型中定义的**语义 law-image**与一次实际运行中观察者能够取得的**档案边界**。两者可以有相同的类型和数值表达，但不因此互相可用。

本卷只讨论有限经典概率模型、有限或可数档案以及声明过的合法续接。它不把语义 law 当成已经交给观察者的输入，不把精确反演称为物理读取，也不把本卷的推导称为 Lean 核验。FIBONACCI_ATOMIC_RELATION_GENERATION.md 提供原子关系、载体和递归生成；[过程几何](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md)提供部分操作、完整行为和任务商；[当前边界的完整续行正规形与有限观察逆](RECURSIVE_RELATIONAL_OBSERVATION_EXACT_CURRENT_BOUNDARY_PROVENANCE.md)、[未知切口与固定未知单位下的初始尾目标直接取得](RECURSIVE_RELATIONAL_OBSERVATION_UNCALIBRATED_TARGET_ACQUISITION.md)以及[原始控制记录取得](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_RECORD_ACQUISITION.md)提供若干实际取得与继续使用的具体合同。

## 1. 语义 law-image 与一次运行的档案

**定义 1.1（共同来源与合法上下文）。** 令 $S$ 是同一实际来源的配置集合，含来源、观察者当前控制、参考、权限和已保留记录。令 $\Theta$ 是可能的完成参数或来源参数。对每个 $\theta\in\Theta$，记 $S_\theta\subseteq S$ 为该参数下的实际配置；不同参数之间不得把各自可达的部分拼成一个新的共同配置。

令 $\Sigma$ 是已经声明的有限合法上下文。它包含允许的初始接入、部分操作、终端读数和失败记录规则。上下文不含一个系统外的全知控制器，也不自动提供重复制备、复制、回滚或 postterminal 操作。

**定义 1.2（语义响应与 law-image）。** 对 $\sigma\in\Sigma$ 和 $\theta\in\Theta$，令

$$
\Lambda_\sigma(\theta)
=
L_{\sigma,\theta}
\in \mathcal L_\sigma
$$

是完整模型对上下文 $\sigma$ 的语义响应。若完整配置还含有不进入该 law 的内部变量，它们仍属于 $S_\theta$，但不因此改变本定义的 law-image。$\mathcal L_\sigma$ 可以是有限 law-vector、完整未归一化 branch mass 表、带失败与 terminal 的概率测度，或任务指定的行为响应。必须在定义中保留任务要求的合法性、失败、输出和记录；只保留成功分布不能替代完整响应。

语义 law-image 是

$$
\operatorname{Im}(\Lambda_\sigma)
=
\{L_{\sigma,\theta}:\theta\in\Theta\}.
$$

它是理论对象。计算出 $L_{\sigma,\theta}$ 或证明 $\theta\mapsto L_{\sigma,\theta}$ 在某个像上可逆，并不表示观察者已经取得了这个 law。

**定义 1.3（实际档案 law）。** 一次合法运行产生记录 $R\in\mathcal R_\sigma$。记录包括合同允许保留的实际输入、操作、读数、失败、terminal、时间标签和后续调用状态；没有实际发生的 branch、完整频率、隐藏量子态或未授权控制不自动属于 $R$。

在参数 $\theta$ 下，$R$ 的分布记为

$$
\mu_{\sigma,\theta}\in\mathsf P(\mathcal R_\sigma).
$$

因此有两个不同层次：

$$
\boxed{
L_{\sigma,\theta}
\quad\text{是响应的语义 law，}\qquad
\mu_{\sigma,\theta}
\quad\text{是一次实际运行档案的 law。}
}
$$

前者可以是后者的统计目标；它不是后者的一个样本值。

**定义 1.4（一次运行的精确取得）。** 令 $B_\sigma$ 是观察者要保存的边界值，语义边界为

$$
\eta_{\rm sem}(\theta)=\eta(L_{\sigma,\theta})\in B_\sigma .
$$

一个确定解码器是 $D:\mathcal R_\sigma\to B_\sigma$。称它在指定参数域上精确取得语义边界，如果

$$
D(R)=\eta_{\rm sem}(\theta)
\quad
\mu_{\sigma,\theta}\text{-几乎处处}
\tag{1.1}
$$

对每个 $\theta$ 成立。随机解码器用一个共同随机核 $K_D(r,\cdot)$；精确取得的等价写法是

$$
(K_D)_\#\mu_{\sigma,\theta}
=
\delta_{\eta_{\rm sem}(\theta)}
\quad
\text{对所有 }\theta .
\tag{1.2}
$$

若只证明 $\theta\mapsto L_{\sigma,\theta}$ 在完整模型的像上有逆，得到的是语义反演，不是式 (1.1) 或 (1.2) 的取得结论。

## 2. 固定的一次返回合同

**定义 2.1（一次返回运行）。** 一次返回合同由以下数据组成：

1. 一个固定来源和一次制备；
2. 一份由观察者实际持有的记录；
3. 一条按声明顺序执行的合法 forward trace；
4. 原始 terminal、失败和成功输出；
5. 允许保存的档案字段及其访问权限。

上下文可以有有限 prefix、intermediate 和 terminal 分支；完整档案必须按合同把这些分支的实际质量或实际记录保留下来。合同不因语义 law 已写在理论正文中，就增加一个 ReadLaw、完整频率表、可选 outcome label、reset、复制或第二次 return。

**定义 2.2（档案更新核）。** 观察者状态写成

$$
o=(c,\kappa,\rho,p),
$$

其中 $c$ 是已取得档案，$\kappa$ 是控制状态，$\rho$ 是实际参考与校准，$p$ 是权限。策略只能由当前状态和实际可访问读数选择：

$$
a=\pi(o).
$$

执行合法操作 $a$ 后取得实际结果 $y$，由核

$$
K_a(y,o'\mid \theta,o)
$$

给出结果与后继状态。未观测的 $\theta$ 不能作为选择器的隐藏输入；如果某个参考、随机种子、来源身份或校准影响结果，就必须列入共同来源和合同。

**命题 2.3（语义表不构成选择器输入）。** 由 $\theta$ 和完整模型计算出的 $L_{\sigma,\theta}$，若没有经过合同允许的取得接口写入 $c,\kappa,\rho,p$，就不能直接用于 $a=\pi(o)$。

**证明。** 选择器的输入域是实际配置中声明的 $o$。把未读取的 $L_{\sigma,\theta}$ 直接传给 $\pi$ 会把一个理论定义转成额外权限，改变合同的配置集合和可执行操作。这个变化不是后处理，而是增加了一个新输入端口。$\square$

## 3. Acquisition square 与动态充分边界

**定义 3.1（取得方块）。** 令 $\operatorname{run}_\sigma$ 把同一实际配置送入一次运行的档案空间：

$$
\operatorname{run}_\sigma:S_\theta\leadsto\mathcal R_\sigma.
$$

波浪箭头表示由运行规则产生的概率核。语义边界和档案解码组成下方的关系图：

$$
\begin{array}{ccc}
S_\theta & \xrightarrow{\ \eta_{\rm sem}\ } & B_\sigma\\
\big\downarrow{\operatorname{run}_\sigma} && \big\uparrow{D}\\
\mathcal R_\sigma & \xrightarrow{\ D\ } & B_\sigma .
\end{array}
$$

方块在概率意义下闭合，指式 (1.2) 对所有声明参数成立。没有方块闭合时，$B_\sigma$ 仍可能是一个良好的语义商，却不能称为已取得边界。

**定义 3.2（动态充分的配置商）。** 设完整配置空间为 $S$，动态摘要为 $\eta_{\rm dyn}:S\to B$，操作为 $T_a$，合法性为 $\operatorname{Leg}(s,a)$，读数为 $y(s,a)$。称 $\eta_{\rm dyn}$ 对指定动作族动态充分，如果存在

$$
\overline{\operatorname{Leg}}(b,a),\qquad
\overline y(b,a),\qquad
\overline T_a:B\to B'
$$

使得对所有 $s\in S$ 有第一式，并且在 $\operatorname{Leg}(s,a)$ 成立时有后两式：

$$
\begin{aligned}
\operatorname{Leg}(s,a)
&=\overline{\operatorname{Leg}}(\eta_{\rm dyn}(s),a),\\
y(s,a)
&=\overline y(\eta_{\rm dyn}(s),a),\\
\eta_{\rm dyn}(T_a(s))
&=\overline T_a(\eta_{\rm dyn}(s)).
\end{aligned}
\tag{3.1}
$$

合法性、标签和后继缺一项都不能把摘要当作可继续运行的边界。

**定理 3.3（取得边界的两项充分条件）。** 假设：

1. 存在动态充分的 $\eta_{\rm dyn}$，且在来源接口上 $\eta_{\rm dyn}(s)$ 与 $\eta_{\rm sem}(\theta)$ 相等，或由已声明的边界同构对应；
2. 取得方块闭合，即存在 $D$ 满足式 (1.2)；
3. 观察者的策略、记录更新和权限更新只使用 $D(R)$ 及合同中另行保留的状态；
4. 每个后续上下文仍在声明的测试族内。

则把一次档案解码为 $b=D(R)$ 后，可以在边界上定义与完整配置相容的合法性、读数、策略和后继；所有指定有限续接在完整配置与边界上产生同样的任务响应。

**证明。** 由 (1.2)，每个参数下的实际档案几乎处处被解码到正确语义边界。由 (3.1)，同一动态边界纤维上的合法性、读数和后继相同，因此策略选择也相同。对续接长度作归纳：零步时响应由 $\eta_{\rm sem}$ 的定义给出；若前缀相同，(3.1) 给出下一步同时合法或同时失败，合法时标签和后继边界相同，记录更新仍相同。测试族封闭保证每个有限外部实验都可归入同一归纳。$\square$

**推论 3.4（语义充分不推出已取得）。** 只满足式 (3.1) 而没有 (1.2) 时，$B$ 只是语义边界；只满足 (1.2) 而没有式 (3.1) 时，解码值可能是已取得的统计量，却不能决定下一步合法性或后继。

这一区分把“边界保存了全部指定未来作用”与“观察者确实拿到了这份边界”分开。

## 4. 共同支持障碍

**定义 4.1（共同支持）。** 对两个参数 $\theta_+,\theta_-$，写

$$
\mu_+\sim\mu_-
$$

如果 $\mu_+$ 与 $\mu_-$ 互相绝对连续。写 $\lambda_\pm=\eta_{\rm sem}(\theta_\pm)$，并假定 $\lambda_+\ne\lambda_-$。

**定理 4.2（共同支持阻止一次运行的零误差取得）。** 若 $\mu_+\sim\mu_-$ 且 $\lambda_+\ne\lambda_-$，则不存在确定解码器 $D$ 使

$$
D_\#\mu_+=\delta_{\lambda_+},
\qquad
D_\#\mu_-=\delta_{\lambda_-};
$$

同样不存在共同随机核 $K_D$ 使

$$
(K_D)_\#\mu_+=\delta_{\lambda_+},
\qquad
(K_D)_\#\mu_-=\delta_{\lambda_-}.
\tag{4.1}
$$

**证明。** 先看确定解码器。令 $E_+=D^{-1}(\{\lambda_+\})$。式 (4.1) 要求 $\mu_+(E_+)=1$ 且 $\mu_-(E_+)=0$，与 $\mu_+\ll\mu_-$ 矛盾。随机核的情形令 $f_\pm(r)=K_D(r,\{\lambda_\pm\})$。零误差要求 $f_+=1$ $\mu_+$-几乎处处、$f_+=0$ $\mu_-$-几乎处处；绝对连续性把这两个几乎处处断言传到同一零集，仍矛盾。$\square$

**定义 4.3（共同基线支配）。** 若存在概率测度 $q$ 和 $0\le\delta<1$，使对所有可测档案事件 $E$：

$$
(1-\delta)q(E)
\le
\mu_\pm(E)
\le
(1+\delta)q(E),
\tag{4.2}
$$

则称 $\mu_+$、$\mu_-$ 被共同基线以系数 $\delta$ 支配。

**定理 4.4（支配、检验风险与共同后处理）。** 在定义 4.3 的条件下：

1. $\mu_+\sim\mu_-$；
2. 以 $1/2,1/2$ 先验进行任意共同二元判别，平均错误率至少为
   $$
   \frac{1-\delta}{2};
   \tag{4.3}
   $$
3. 对任意共同随机后处理核 $K$，
   $$
   \operatorname{TV}(K_\#\mu_+,K_\#\mu_-)
   \le
   \operatorname{TV}(\mu_+,\mu_-)
   \le\delta;
   \tag{4.4}
   $$
4. 若一个三值随机解码器输出 $\{+,-,\bot\}$，且两种参数下都不允许错误的有标签输出，则两种参数下的有标签成功概率都为零。

**证明。** (4.2) 先给出相互绝对连续。若以 $q$ 为基准写密度 $r_\pm$，则 $1-\delta\le r_\pm\le1+\delta$，所以

$$
\operatorname{TV}(\mu_+,\mu_-)
=\frac12\int|r_+-r_-|\,dq
\le\delta.
$$

二元判别的平均错误率等于 $\frac12(1-\operatorname{TV})$ 的下界，给出 (4.3)。总变差的数据处理不等式给出 (4.4)。最后，零错误要求输出 $+$ 的概率在 $\mu_-$ 下为零；绝对连续性把同一事件在 $\mu_+$ 下也变成零。对输出 $-$ 同理，故只能输出 $\bot$。$\square$

**推论 4.5（完整 law-vector 的单坐标见证）。** 若 $\lambda_+\ne\lambda_-$，取一个坐标或可测事件 $j$ 使

$$
\lambda_+(j)\ne\lambda_-(j).
$$

任何一次运行中对完整 law-vector 的精确取得都会给出一个区分 $\theta_+$ 与 $\theta_-$ 的零误差解码器。因此，定理 4.2 已足以阻止整个向量的零误差取得；不必先恢复所有坐标。

## 5. 语义可分离与实际不可取得可以并存

**命题 5.1（有限样本的最小例子）。** 令语义参数为 $\theta\in\{+,-\}$，每个参数的语义输出 law 为

$$
L_+(1)=p_+,\qquad L_-(1)=p_-,
\qquad 0<p_-<p_+<1.
$$

一次实际运行只返回一个 bit $R\in\{0,1\}$，且

$$
\mu_\theta(R=1)=L_\theta(1).
$$

则 $L_+\ne L_-$，但 $\mu_+\sim\mu_-$，所以一次记录不能零误差恢复语义 law。

**证明。** 两个 law 在两个记录值 $0,1$ 上都有正质量，故互相绝对连续；定理 4.2 适用。$\square$

这不是“语义 law 没有区别”。它说明 law 的不同是统计区别，而单次记录没有把该区别编码为零误差可读的状态。

**命题 5.2（有限重复仍不自动产生零误差）。** 在命题 5.1 的条件下，$n$ 次独立同源运行的档案 law 为 $\mu_+^{\otimes n}$ 与 $\mu_-^{\otimes n}$。对每个有限 $n$，二者仍互相绝对连续，因此不存在有限次零误差 law 解码器。

**证明。** 两个有限乘积的每个点质量仍为正，故互相绝对连续；应用定理 4.2。自适应协议也只有在每一步条件档案 law 保持相互绝对连续时，才能用同一乘积论证。$\square$

正误差估计、样本数增加以及渐近区分属于另一个任务。它们不能被零误差取得的否定替代，也不能反向证明一次运行已经含有精确 law。

**命题 5.3（语义边界可能进一步忘记完整完成）。** 即使式 (1.2) 成立，若存在 $J\ne J'$ 但

$$
\eta_{\rm sem}(J)=\eta_{\rm sem}(J'),
$$

则该边界只恢复指定 law quotient，不能恢复完整 completion。要恢复 $J$，必须扩大未来测试族或边界字段，使该纤维被切开。

**证明。** 由相同边界值，任何边界解码器对 $J,J'$ 输出相同；若任务要求区分二者，则它不可能同时正确。$\square$

## 6. 当前信息与未来可用关系

**命题 6.1（暂时零信息的关系记录）。** 令 $X,K$ 是独立均匀 bit。观察者第一次取得

$$
Y=X\oplus K.
$$

则

$$
I(X;Y)=0.
$$

若之后合法取得 $K$，则

$$
X=Y\oplus K,
\qquad
I(X;Y,K)=1.
$$

**证明。** $Y$ 是均匀 bit 且与 $X$ 独立，所以第一式成立；第二式是异或恒等式。$\square$

若边界只保存当前关于 $X$ 的后验，则 $Y=0$ 与 $Y=1$ 都给相同后验，却要求在未来读到同一个 $K$ 时使用不同的解码。故动态充分边界必须保留会影响未来合法读数的联合关系、参考、权限和控制状态，而不只是一个当前熵值或当前后验。

**推论 6.2（边界字段的最小角色）。** 对一个含隐藏参考的任务，边界至少要能表示：

$$
\boxed{
\text{当前证据}
\;+\;
\text{与未来读数有关的联合关系}
\;+\;
\text{控制与权限}.
}
$$

这些字段必须来自同一个实际来源。把不同可能来源中的最好证据拼成一份摘要，不满足共同实现条件。

## 7. 四种表达及其互相恢复

把当前关系结构的四种表达记为：

- **载体/空间** $X$：来源、端口和合法连接图；
- **过程/时间** $T$：按合法接续排序的 trace、事件词和路径累积量；
- **语义边界** $B_{\rm sem}$：指定未来测试下的行为或 law quotient；
- **实际记忆** $M$：一次运行中真实取得并保留的档案、控制与权限。

**定理 7.1（四表达的恢复合同）。** 对一个固定任务族，若同时满足：

1. 载体上的合法操作形成有类型的部分过程；
2. $B_{\rm sem}$ 满足动态充分条件 (3.1)；
3. trace 到过程记忆的编码在行为等价意义下是单射，并保留必要的标签和累积量；
4. 存在取得解码器满足 (1.2)；
5. 记忆更新对所有指定未来测试保持同一行为纤维的合法性、读数和后继；

则在该任务族内：

- 由载体和合法接续可以构造过程 trace；
- 由完整模型的 trace family 与响应 law 可以得到语义边界行为；单次实际 trace 只给档案；
- 由实际记忆可以取得同一边界值并继续执行；
- 边界不能恢复被任务商刻意忘掉的 full state。

**证明。** 第 1 项给过程定义。第 2 项使语义边界上的更新良定。第 3 项使 trace 的事件词、费用和钟读数在行为商上下降。第 4 项闭合 acquisition square。第 5 项按续接长度归纳，保证边界与记忆的后续选择一致。最后，若两个 full state 处于同一行为纤维，任何指定任务都给出相同响应，恢复 full state 超出该任务的边界。$\square$

**命题 7.2（缺一项的反例方向）。**

- 没有动态充分性：当前摘要可能相同，但下一步合法性或后继不同；
- 没有 trace 编码：相同端点可能隐藏不同事件档案和路径累积量；
- 没有取得方块：语义 law 可以可逆，但观察者没有 law 输入；
- 没有记忆更新条件：当前边界可用，下一步却因遗忘参考而失效。

这些不是四种物理对象的四个独立宇宙，而是同一关系网络上不同的投影和访问合同。

## 8. 直接扩大的取得接口

**定义 8.1（预制备 LawRead_L）。** 固定有限坐标族 $j=1,\ldots,L$。LawRead_L 是一个在制备前已声明的接口，返回

$$
\bigl(L_{\sigma,\theta}(1),\ldots,L_{\sigma,\theta}(L)\bigr)
$$

或一个带明确误差、置信度和失败标记的估计。接口必须同时声明：

- 参数绑定和校准来源；
- 返回值是否来自同一实际来源；
- 选择器可访问的时间和权限；
- 存储、校验、调用和后继成本；
- 未命中或参数在 law-image 外时的行为。

当这些 law 行恰好构成 $B_{\rm sem}$，或合同另行给出它们到 $B_{\rm sem}$ 的解码器，并且参数绑定与后继条件满足时，取得方块才可以闭合。这个接口是新增资源，不能从语义反演、普通 Read 或已有矩阵公式自动推出。

**定义 8.2（重复同源制备接口）。** 允许固定未知参数下的真实重复制备，得到 $R_1,\ldots,R_n$ 及其身份、联合 law、采样成本和估计误差。仅仅说“可以重复”不足以构造接口；来源绑定、独立性或相关性、合法选择、保留历史和继续调用都要写进合同。

**命题 8.3（扩大接口不等于完成原接口）。** 若原始一次运行的 archive laws 互相绝对连续，而新增 LawRead_L 返回精确 law rows，则新增模型可以拥有零误差 law boundary；这说明原始障碍来自取得接口，而不是语义 law-image 的数学不可定义。它不证明原始装置已经具有该接口。

## 9. 与原子生成和现有卷的关系

FIBONACCI_ATOMIC_RELATION_GENERATION.md 的两个原子 $\alpha,\beta$ 可以作为最底层生成语法。它们供应 carrier、结构递归和合法替换；经过 Process Geometry 的行为商后，才得到任务相关的语义边界。原子生成不自动供应一次运行的概率 law、LawRead、统计频率或 law decoder。

PRIOR_ACQUISITION_BOUNDARY.md 已区分边界的被动预测与选择下一次 Read；本卷把这个区别提升为式 (1.2) 的 acquisition square。ACQUIRED_INTRINSIC_DEPTH_CALIBRATION.md 和 ORIGINAL_CONTROL_RECORD_ACQUISITION.md 给出实际记录、权利、资源和同源继续使用的具体实现域；它们不因此提供任意语义 law 的一次运行解码器。UNIFORM_DESCRIPTOR_BOUNDARY.md 的 exact Reply、whole-row Same 和动态边界条件，对应本卷的式 (3.1)。

因此当前最精简的分层可写成：

$$
\boxed{
(\alpha,\beta)
\;\longrightarrow\;
(\text{合法接续},\text{trace})
\;\longrightarrow\;
(\text{行为商},\text{semantic law-image})
\;\longrightarrow\;
(\text{archive kernel},\text{acquisition interface}).
}
\tag{9.1}
$$

最后一层不是前一层的记号改写；它决定语义边界是否真的成为观察者能够保存和继续使用的边界。

## 10. 范围与未决桥梁

本卷证明和反例都限于已经声明的任务族、共同来源和实际档案合同。它们不宣称：

- 对所有装置或所有 quantum completion 的普遍 no-go；
- full completion 或 full unitary 的恢复；
- LawRead_L 的物理安装；
- $\alpha,\beta$ 的普遍不可约最小性；
- 空间度量、物理时间或经验规律已经由关系商自动产生；
- 理论正文已经得到 Lean/kernel 验证。

仍需研究的桥梁是：对具体 FIBONACCI_ATOMIC_RELATION_GENERATION 载体，构造一个不偷渡 law 输入的实际 archive kernel；证明哪些语义边界在合法续接下动态闭合；再判断是否存在有限 LawRead_L、重复同源制备或其他真实接口，使 acquisition square 在目标任务上闭合。这个问题比“语义 law 是否可反演”更接近内部观察者的实际能力，也更直接连接空间、时间、边界和记忆的互相恢复。

## 追加锚（本行以下为增补区）

