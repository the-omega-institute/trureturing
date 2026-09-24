# 白盒的纤维律：损失看不见的部分由正则项裁决
## White-Box Loss-Fiber Law（WLFL）v1.0

> **本卷的机器契约（逐条可查，落地后不改）。** 消化器 `generic-v1`；地址（locator）由 `tools/StrataLint.Engine/Digestion/Atomizers/GenericAtomizer.cs` 仅从本文件的字节算出，不查任何词表。本卷只增不减：卷首恒定区与既有各章一经合入即一字不改，全部修订、勘误、增补一律写在文末追加锚之后的新章里。旧章保留为历史记录；勘误的形式是新章点名旧编号并给出改判，不是回去改旧字节（CLAUDE.md 第 1.2 条、第 4.2 条）。

## 1. 定位、状态与产地

**参考输入，不是真源。** 本卷是 trureturing 的参考输入：提供出处与灵感，不承担机器治理，Lean 形式化才是唯一真源。不得把任何形式化工件反向绑定到本卷的章节号或定理号上（第 4.3 条）。本卷与[机器学习主卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)（下称 ML 卷）共用“读数—纤维—因子化”的语言，并直接使用[《递归关系观察》](RECURSIVE_RELATIONAL_OBSERVATION.md)（下称 RRO）第 2 节的逃逸集与精确因子化定理；本卷不重建那套框架，只把它对准两个具体的白盒现象。

**证明状态。** 本卷给出的是 ZFC 内的普通数学散文与第 8 章的有限精确核验。本卷未经 Lean kernel 验证，不得称 kernel-verified；哪条已被形式化，以冻结账本为准，不以本卷自述为准（第 2.4 条）。凡标 `repo-derived` 者为本卷自证；标 `literature-attested` 者以所引文献为准，本卷不重证；标 `suspected-novel` 者是认真检索后未见于文献的条目，检索范围写在第 7 章。

**产地（第 5.2 条三项，写实，缺项即不完整）。** ①skill 上下文：`theory-volume-template`（卷骨架与追加纪律）；未使用 `consensus-rnd:sshx` 编排协议。②载体与分工：全部正文、证明与第 8 章核验脚本由 claude 主循环（Claude Fable 5.1）亲撰并亲跑；文献地图由主循环经 `tools/scripts/agent/nyx.sh` 向 GPT Pro 派出三条检索票，arXiv 编号由主循环逐条在线解析核对。③混合方式与核验范围：独立评审席为 codex-cli 隔离席（与主循环非同模型族），并发盲评；票数、分歧与裁决记于第 7 章“评审结论”一栏；主循环亲验的只有核验脚本的退出码与哨兵、以及 arXiv 编号的解析结果，评审席声称跑过的东西一律按席位自报计。

**读法。** 本卷按写作时序排列：第 1–8 章是基线叙述，其后每一批增补自带一节“本批导航”，说明它扩充、限定或改判了前文的哪一条。基线叙述中的“本次”“本轮”一律指写下它的那一次工作，不随后续增补改写。

**一句话。** 一个被优化的目标 $\mathcal J=L+\lambda R$ 里，主损失 $L$ 只看得见自己的像；在 $L$ 的一条纤维（同一 $L$ 值、尤其是零集）内部，一切差别都对 $L$ 不可见，于是纤维内的选择完全由正则项 $R$ 裁决。本卷把两个著名的白盒谜题写成这条律的两个精确实例：**延迟泛化**（训练损失早已平坦、测试误差很久之后才下降）是训练读数的纤维坐标在权重衰减下的指数衰减，其时刻对训练曲线可证地不可见；**特征吸收**（稀疏自编码器把父特征吸进子特征的原子里）是重构损失的纤维内 $\ell_1$ 几何对“出现过的点”而非“生成它的方向”的偏好。两者的共同形状是：白盒能看见纤维坐标，黑盒只能看见像。

## 2. 记号与约定

**约定 2.1（读数、纤维与逃逸集）。** 对映射 $q:X\to Q$，其在 $z\in q[X]$ 处的纤维是 $q^{-1}(z)$。对目标 $T:X\to Y$，逃逸集按 RRO 定义 2.1 取 $\mathcal E(q;T)=\{(x,x')\in X^2:q(x)=q(x')\land T(x)\ne T(x')\}$；RRO 定理 2.2 说 $\mathcal E(q;T)=\varnothing$ 当且仅当 $T$ 经 $q$ 唯一因子化。本卷把“$T$ 对 $q$ 不可见”与“$\mathcal E(q;T)\ne\varnothing$”当作同一句话。凡说“某量对训练损失曲线不可见”，都指以整条曲线 $t\mapsto L(\theta(t))$ 为 $q$ 时该量的逃逸集非空。

**约定 2.2（线性模型）。** 特征映射 $\varphi:\mathcal X\to\mathbb R^p$；模型 $f_\theta(x)=\varphi(x)^\top\theta$。训练集 $(x_i,y_i)_{i\le N}$ 给出 $\Phi\in\mathbb R^{N\times p}$（第 $i$ 行 $\varphi(x_i)^\top$）与 $y\in\mathbb R^N$，恒设 $N\le p$ 且 $\Phi$ 行满秩，奇异值 $\sigma_1\ge\cdots\ge\sigma_N>0$。$P=\Phi^\top(\Phi\Phi^\top)^{-1}\Phi$ 是到行空间 $\operatorname{row}\Phi$ 的正交投影，$P^\perp=I-P$ 投到 $\ker\Phi$。训练损失 $L(\theta)=\tfrac12\|\Phi\theta-y\|^2$，带权重衰减的梯度流为
$$
\dot\theta=-\Phi^\top(\Phi\theta-y)-\lambda\theta,\qquad\lambda\ge0 .
$$
记 $\theta_\lambda=\Phi^\top(\Phi\Phi^\top+\lambda I)^{-1}y$（岭解），$\theta_0=\Phi^\top(\Phi\Phi^\top)^{-1}y$（最小范数插值解）。对测试点 $x$ 记 $a(x)=\varphi(x)^\top\theta_\lambda-y(x)$（岭误差）与 $b(x)=\varphi(x)^\top P^\perp\theta(0)$（初始化中逃逸到 $\ker\Phi$ 的分量在 $x$ 处的读数）。

**约定 2.3（字典学习）。** 数据 $x$ 取自 $\mathbb R^d$ 上有限支撑的分布。字典 $D=[d_1,\dots,d_K]$，各原子单位范数 $\|d_k\|_2=1$；码 $c\in\mathbb R^K_{\ge0}$。两阶段目标
$$
\operatorname{cost}(x;D)=\min_{c\ge0}\Big[\tfrac12\|x-Dc\|_2^2+\lambda\|c\|_1\Big],\qquad
\mathcal J(D)=\mathbb E_x\operatorname{cost}(x;D),\qquad 0<\lambda<1 .
$$
这是稀疏自编码器目标去掉摊销编码器后的内层精确形式；摊销编码器只能使目标更大，故本卷结论是对理想编码器的结论。取 $u,v$ 为标准正交单位向量，$w=(u+v)/\sqrt2$；数据支撑于 $\{0,u,u+v,v\}$，概率 $p_0,p_A,p_{AB},p_B$，其中 $p_B$ 是“B 单独出现”的概率，$p_B=0$ 称严格层级（B 蕴含 A）。两个典型字典：忠实字典 $D_F=[u,v]$ 与吸收字典 $D_A=[u,w]$。

## 3. 读数纤维与正则裁决

**定义 3.1（切向逃逸空间）。** 设 $F:\mathbb R^p\to\mathbb R^N$ 可微，$L(\theta)=\tfrac12\|F(\theta)-y\|^2$，零集 $Z=F^{-1}(y)$。对 $\theta\in Z$，令 $J=DF(\theta)$，切向逃逸空间 $K(\theta)=\ker J$。当 $J$ 在 $\theta$ 的邻域上秩恒定时 $Z$ 是子流形且 $T_\theta Z=K(\theta)$。

**命题 3.2（损失对切向逃逸三阶盲，repo-derived）。** 设 $F$ 二次连续可微，$\theta\in Z$，$v\in K(\theta)$。则 $\varepsilon\mapsto L(\theta+\varepsilon v)$ 在 $\varepsilon=0$ 处的一、二、三阶导数全为零，且 $L(\theta+\varepsilon v)=O(\varepsilon^4)$。

证明。$F(\theta+\varepsilon v)-y=\varepsilon Jv+\varepsilon^2 r(\varepsilon)$，其中 $r$ 在 $0$ 附近有界（Taylor 余项）。$Jv=0$ 给 $F(\theta+\varepsilon v)-y=\varepsilon^2r(\varepsilon)$，故 $L=\tfrac12\varepsilon^4\|r(\varepsilon)\|^2$，前三阶导数为零。证毕。

**定理 3.3（零集上的静态裁决，literature-attested：Tikhonov 正则化极限）。** 设 $\Theta$ 紧，$L,R:\Theta\to\mathbb R$ 连续，$\Theta_0=\arg\min L\ne\varnothing$。取 $\lambda_k\downarrow0$ 与 $\theta_k\in\arg\min(L+\lambda_kR)$。则 $(\theta_k)$ 的任一极限点 $\bar\theta$ 满足 $\bar\theta\in\arg\min_{\Theta_0}R$。

证明。取 $\theta^\star\in\arg\min_{\Theta_0}R$，$L^\star=\min L$。由 $\theta_k$ 的最优性，$L(\theta_k)+\lambda_kR(\theta_k)\le L^\star+\lambda_kR(\theta^\star)$。因 $L(\theta_k)\ge L^\star$，得 $R(\theta_k)\le R(\theta^\star)$；又 $R$ 在紧集上有界，得 $L(\theta_k)\le L^\star+\lambda_k(R(\theta^\star)-R(\theta_k))\to L^\star$。沿子列取极限并用连续性：$L(\bar\theta)=L^\star$ 且 $R(\bar\theta)\le R(\theta^\star)$。这是 Tikhonov 正则化的经典极限性质，见第 7 章表；本卷只用其陈述。证毕。

**定理 3.4（零集上的瞬时动态裁决，repo-derived）。** 设 $R$ 可微，$\theta\in Z$，考虑流 $\dot\theta=-\nabla L(\theta)-\lambda\nabla R(\theta)$。则在 $\theta$ 处 $\dot\theta=-\lambda\nabla R(\theta)$，其切向分量为 $-\lambda P_{K(\theta)}\nabla R(\theta)$，法向分量为 $-\lambda P_{K(\theta)^\perp}\nabla R(\theta)$；此时 $\frac{d}{dt}L(\theta(t))=0$。取 $R=\tfrac12\|\theta\|^2$ 时切向分量为 $-\lambda P_{K(\theta)}\theta$。

证明。$\theta\in Z$ 给 $\nabla L(\theta)=J^\top(F(\theta)-y)=0$，故速度只剩正则项，按 $K(\theta)\oplus K(\theta)^\perp$ 分解即得两分量。$\frac{d}{dt}L=\langle\nabla L,\dot\theta\rangle=0$。这是一个逐点陈述：离开 $Z$ 之后 $\nabla L$ 重新出现，长期行为要靠具体模型（第 4 章给线性模型的精确解；非线性情形的极限流形流是文献结果，第 7 章标注，本卷不重证）。证毕。

**评注 3.5（纤维律，semantic）。** 定理 3.3 与 3.4 是同一句话的静态形与动态形：主损失 $L$ 以其像为读数，纤维内部对它不可见；在纤维内挑选的是 $R$。白盒解释的对象恰是纤维坐标——它们可从参数直接读出，但不出现在任何只依赖 $L$ 的曲线里。下面两章分别用训练损失（第 4 章）与重构损失（第 5 章）作 $L$。

## 4. 线性化模型的精确解与延迟泛化

**定理 4.1（精确分解，repo-derived）。** 在约定 2.2 下，对任意 $\theta(0)\in\mathbb R^p$ 与 $\lambda\ge0$，流的唯一解为
$$
\theta(t)=\theta_\lambda+e^{-(\Phi^\top\Phi+\lambda I)t}\big(P\theta(0)-\theta_\lambda\big)+e^{-\lambda t}P^\perp\theta(0),
$$
其中前两项恒在 $\operatorname{row}\Phi$ 内，第三项恒在 $\ker\Phi$ 内；$\Phi^\top\Phi+\lambda I$ 限制到 $\operatorname{row}\Phi$ 的特征值为 $\sigma_i^2+\lambda$。（$\lambda=0$ 时把 $\theta_\lambda$ 读作 $\theta_0$。）

证明。$\Phi^\top(\Phi\theta-y)\in\operatorname{row}\Phi$，故 $P^\perp\dot\theta=-\lambda P^\perp\theta$，得第三项。行分量满足 $\dot\theta_r=-(\Phi^\top\Phi+\lambda I)\theta_r+\Phi^\top y$，其中 $\Phi\theta=\Phi\theta_r$；$\operatorname{row}\Phi$ 是 $\Phi^\top\Phi$ 的不变子空间，其上该算子的谱为 $\{\sigma_i^2\}$。不动点 $(\Phi^\top\Phi+\lambda I)^{-1}\Phi^\top y=\Phi^\top(\Phi\Phi^\top+\lambda I)^{-1}y=\theta_\lambda$（推移恒等式），线性常系数方程的解唯一。$\lambda=0$ 时算子在 $\operatorname{row}\Phi$ 上仍正定，不动点为 $\theta_0$。证毕。

**推论 4.2（训练曲线只依赖行分量；平台值，repo-derived）。** 训练损失曲线 $t\mapsto L(\theta(t))=\tfrac12\|\Phi\theta_r(t)-y\|^2$ 只依赖 $P\theta(0)$，与 $P^\perp\theta(0)$ 无关；且
$$
L(\theta(t))\to L_\infty=\tfrac{\lambda^2}{2}\big\|(\Phi\Phi^\top+\lambda I)^{-1}y\big\|^2\le\frac{\lambda^2\|y\|^2}{2(\sigma_N^2+\lambda)^2},
$$
收敛速率不慢于 $e^{-(\sigma_N^2+\lambda)t}$。

证明。$\Phi P^\perp=0$ 给第一句。$\Phi\theta_\lambda-y=\Phi\Phi^\top(\Phi\Phi^\top+\lambda I)^{-1}y-y=-\lambda(\Phi\Phi^\top+\lambda I)^{-1}y$，取范数并用 $\Phi\Phi^\top+\lambda I\succeq(\sigma_N^2+\lambda)I$。瞬态项由定理 4.1 的指数因子控制。证毕。

**定理 4.3（成对实例：泛化时刻对训练曲线不可见，repo-derived）。** 设 $v\in\ker\Phi$，$v\ne0$，$\lambda\ge0$。初始化 $\theta(0)$ 与 $\theta(0)+v$ 的训练损失曲线在所有 $t\ge0$ 逐点相等，而它们在任一满足 $\varphi(x)^\top v\ne0$ 的测试点上的预测相差 $e^{-\lambda t}\varphi(x)^\top v$。因此，以整条训练曲线为读数 $q$，任何依赖 $P^\perp\theta(0)$ 的测试统计量 $T$（例如某测试点预测首次进入给定容差的时刻）都有 $\mathcal E(q;T)\ne\varnothing$，按 RRO 定理 2.2 不存在把 $T$ 表成训练曲线之函数的方式。

证明。$P(\theta(0)+v)=P\theta(0)$，由定理 4.1 两条轨迹的行分量逐点相等，故训练残差相等；零空间分量相差 $e^{-\lambda t}v$，作用到 $\varphi(x)$ 得预测之差。两条轨迹给出 $q$ 相同而 $T$ 不同的一对，即逃逸集非空。证毕。

**定理 4.4（测试预测的两指数形式与延迟时刻，repo-derived）。** 记 $s(t)=e^{-\lambda t}$，$E(t)=e^{-(\Phi^\top\Phi+\lambda I)t}(P\theta(0)-\theta_\lambda)$。对任意测试点 $x$，
$$
f_{\theta(t)}(x)-y(x)=a(x)+s(t)\,b(x)+\varphi(x)^\top E(t),\qquad
\|E(t)\|\le e^{-(\sigma_N^2+\lambda)t}\|P\theta(0)-\theta_\lambda\| .
$$
对有限测试集，$L_{\rm test}(t)=\tfrac12\sum_x\big(a(x)+s(t)b(x)+\varphi(x)^\top E(t)\big)^2$。若忽略 $E$ 项（其衰减率 $\sigma_N^2+\lambda$ 远大于 $\lambda$），则 $L_{\rm test}$ 是 $s$ 的二次函数 $L_\infty^{\rm test}+2s\langle a,b\rangle+s^2\|b\|^2$，其中 $\langle a,b\rangle=\sum_xa(x)b(x)$。由此：
（i）给定容差 $\varepsilon>0$ 与测试点 $x$，逃逸读数 $|s(t)b(x)|$ 首次不超过 $\varepsilon$ 的时刻为 $T_\varepsilon(x)=\max\{0,\lambda^{-1}\log(|b(x)|/\varepsilon)\}$；
（ii）把 $P^\perp\theta(0)$ 换成 $sP^\perp\theta(0)$（$s>1$）而不动 $P\theta(0)$，则每个 $T_\varepsilon(x)>0$ 恰增加 $\lambda^{-1}\log s$，训练曲线不变；
（iii）$L_{\rm test}(t)-L_\infty^{\rm test}$ 的渐近衰减率在 $\langle a,b\rangle\ne0$ 时为 $\lambda$，在 $\langle a,b\rangle=0$ 时为 $2\lambda$；任一有限窗口上的对数斜率介于 $-2\lambda$ 与 $-\lambda$ 之间（当 $\langle a,b\rangle\ge0$）；
（iv）快慢两个时间尺度之比为 $(\sigma_N^2+\lambda)/\lambda$：训练残差在 $1/(\sigma_N^2+\lambda)$ 量级内到达平台，逃逸分量在 $1/\lambda$ 量级内衰减。

证明。把定理 4.1 代入 $\varphi(x)^\top\theta(t)$ 并减去 $y(x)$ 即得分解；$E$ 的范数界来自谱下界。二次形式由展开得到。（i）是 $s(t)|b(x)|=\varepsilon$ 的解；（ii）$b(x)$ 变为 $sb(x)$，$\log$ 相加，训练曲线由推论 4.2 不变；（iii）$2s\langle a,b\rangle+s^2\|b\|^2$ 中 $s\to0$ 时线性项主导除非其系数为零，窗口斜率是两项斜率的加权平均；（iv）由推论 4.2 与定理 4.1 第三项的速率读出。证毕。

**命题 4.5（无正则项则无晚期，repo-derived）。** $\lambda=0$ 时 $P^\perp\theta(t)\equiv P^\perp\theta(0)$，且 $f_{\theta(t)}(x)=\varphi(x)^\top\theta_0+b(x)+\varphi(x)^\top E(t)$，其中 $\|E(t)\|\le e^{-\sigma_N^2t}\|P\theta(0)-\theta_0\|$。故在 $t\gg1/\sigma_N^2$ 之后测试预测不再变化：固定特征、无正则项的线性模型不存在晚于训练收敛的泛化改善。

证明。定理 4.1 取 $\lambda=0$。证毕。

**命题 4.6（逃逸范数是白盒进度量，repo-derived）。** $\|P^\perp\theta(t)\|=e^{-\lambda t}\|P^\perp\theta(0)\|$ 可由参数直接算出，严格单调、对数线性，而按推论 4.2 它对训练损失曲线不可见。忽略 $E$ 项后，测试损失是它的二次函数（定理 4.4），故它与 $\langle a,b\rangle$、$\|b\|^2$ 三个量一起决定测试损失的整条晚期曲线。

证明。定理 4.1 第三项取范数；其余由定理 4.4 直接读出。证毕。

**命题 4.7（线性化网络的对应与失效时刻，repo-derived 的记账；线性化本身 literature-attested）。** 对可微网络在 $\theta_0$ 处线性化 $f_\theta(x)\approx f_{\theta_0}(x)+\varphi(x)^\top(\theta-\theta_0)$，$\varphi(x)=\nabla_\theta f_\theta(x)|_{\theta_0}$，并对 $\theta$ 施加权重衰减，则在线性化模型内测试预测的零空间部分为
$$
f_{\theta_0}(x)-\varphi(x)^\top P^\perp\theta_0+e^{-\lambda t}\varphi(x)^\top P^\perp\theta_0 ,
$$
即只有初始函数沿 $P^\perp\theta_0$ 的线性部分衰减，常数 $f_{\theta_0}(x)-\varphi(x)^\top P^\perp\theta_0$ 在线性化模型里永不衰减（对一次齐次网络该常数等于 $\varphi(x)^\top P\theta_0$）。同时，线性化只在 $\|\theta(t)-\theta_0\|$ 小时有效，而零空间分量在 $\lambda t=O(1)$ 时已变化常数倍：**线性化失效的时刻与延迟泛化发生的时刻同阶**。故对非线性网络本章是一阶图景，不是定理。

证明。令 $\delta=\theta-\theta_0$，流为 $\dot\delta=-\Phi^\top(\Phi\delta+f_{\theta_0}(X)-y)-\lambda(\delta+\theta_0)$；零空间分量 $\dot\delta_n=-\lambda(\delta_n+P^\perp\theta_0)$，$\delta_n(0)=0$，解 $\delta_n(t)=-(1-e^{-\lambda t})P^\perp\theta_0$，代回即得。一次齐次时 Euler 恒等式给 $f_{\theta_0}(x)=\varphi(x)^\top\theta_0$。失效时刻的陈述是对 $\|\delta_n(t)\|=(1-e^{-\lambda t})\|P^\perp\theta_0\|$ 的直接读数。线性化的适用条件见第 7 章所引 NTK 文献。证毕。

## 5. 稀疏字典学习中的吸收

**引理 5.1（单点下界与对齐等式，repo-derived）。** 在约定 2.3 下，对任意 $x\ne0$、任意单位范数字典 $D$ 与 $0<\lambda<\|x\|$，
$$
\operatorname{cost}(x;D)\ \ge\ \lambda\|x\|-\tfrac12\lambda^2 ,
$$
等号成立当且仅当 $D$ 含原子 $x/\|x\|$；此时最优码把 $\|x\|-\lambda$ 放在该原子上、其余为零。

证明。对任意 $c\ge0$ 记 $r=\|x-Dc\|$。三角不等式与单位范数给 $\|x\|\le\|Dc\|+r\le\sum_kc_k\|d_k\|+r=\|c\|_1+r$，故目标 $\ge\tfrac12r^2+\lambda(\|x\|-r)\ge\lambda\|x\|-\tfrac12\lambda^2$，后一步在 $r=\lambda$ 取最小。等号要求 $\|Dc\|=\|c\|_1$（所有活跃原子相同）、$r=\lambda$ 且 $x-Dc$ 与 $Dc$ 同向（三角不等式取等），即 $Dc=(\|x\|-\lambda)x/\|x\|$，活跃原子只能是 $x/\|x\|$。反之若该原子在字典里，取该码即达下界。证毕。

**定理 5.2（严格层级下吸收全局最优，repo-derived）。** 数据支撑于 $\{0,u,u+v\}$，$p_A,p_{AB}>0$，$0<\lambda<1$。则在所有单位范数字典（任意原子数）上
$$
\min_D\mathcal J(D)=p_A\big(\lambda-\tfrac12\lambda^2\big)+p_{AB}\big(\sqrt2\lambda-\tfrac12\lambda^2\big),
$$
取到最小值当且仅当 $D$ 同时含原子 $u$ 与 $w$。忠实字典 $D_F=[u,v]$ 严格次优，差额恰为 $p_{AB}\lambda(2-\sqrt2-\lambda/2)>0$。

证明。对每个数据点用引理 5.1：$\|u\|=1$、$\|u+v\|=\sqrt2$，下界之和即右端，等号当且仅当两原子都在。对 $D_F$，原子正交，$\operatorname{cost}(u+v;D_F)=\min_{c\ge0}\tfrac12[(1-c_1)^2+(1-c_2)^2]+\lambda(c_1+c_2)$ 按坐标分离，各在 $1-\lambda$ 取到 $\lambda-\tfrac12\lambda^2$，合计 $2\lambda-\lambda^2$；减去 $\sqrt2\lambda-\tfrac12\lambda^2$ 得 $\lambda(2-\sqrt2-\lambda/2)$，因 $2-\sqrt2>\tfrac12$ 而对 $\lambda<1$ 为正。证毕。

**命题 5.3（深度 $m$ 的层级，repo-derived）。** 设 $x=u_1+\cdots+u_m$，$u_i$ 标准正交，$m\ge2$，$0<\lambda<1$。以 $x/\sqrt m$ 为原子的费用为 $\sqrt m\lambda-\tfrac12\lambda^2$；以 $u_1,\dots,u_m$ 为原子分解 $x$ 的费用为 $m(\lambda-\tfrac12\lambda^2)$；二者之差 $\lambda(m-\sqrt m)-\tfrac12(m-1)\lambda^2$ 对 $\lambda<1$ 恒正。

证明。前者由引理 5.1 的等号情形；后者按坐标分离同定理 5.2。差为正当且仅当 $\lambda<2(m-\sqrt m)/(m-1)$，而右端在 $m=2$ 时为 $4-2\sqrt2>1$ 且随 $m$ 单调增到 $2$。证毕。

**定理 5.4（两典型字典的精确比较，repo-derived）。** 在约定 2.3 的四点支撑上，对 $0<\lambda<1$，
$$
\mathcal J(D_A)-\mathcal J(D_F)=p_B\,\Delta_v(\lambda)-p_{AB}\,\lambda\Big(2-\sqrt2-\frac\lambda2\Big),\qquad
\Delta_v(\lambda)=\begin{cases}\tfrac14-\big(1-\tfrac1{\sqrt2}\big)\lambda,&\lambda\le\tfrac1{\sqrt2},\\[2pt]\tfrac12-\lambda+\tfrac12\lambda^2,&\tfrac1{\sqrt2}\le\lambda<1.\end{cases}
$$
故在两者之间吸收字典更优当且仅当 $p_B/p_{AB}<\rho^\ast(\lambda)=\lambda(2-\sqrt2-\lambda/2)/\Delta_v(\lambda)$；$\rho^\ast(0.1)\approx0.243$，$\rho^\ast(0.3)\approx0.806$。

证明。目标关于 $c\ge0$ 严格凸，KKT 条件充分：活跃原子的相关 $\langle x-Dc,d_k\rangle=\lambda$，非活跃原子的相关 $\le\lambda$。$D_F$ 下三点费用分别为 $\lambda-\tfrac12\lambda^2$（$u$）、$2\lambda-\lambda^2$（$u+v$）、$\lambda-\tfrac12\lambda^2$（$v$）。$D_A=[u,w]$ 下：$x=u$ 取 $c=(1-\lambda,0)$，残差 $\lambda u$ 与 $w$ 的相关 $\lambda/\sqrt2\le\lambda$，费用 $\lambda-\tfrac12\lambda^2$；$x=u+v=\sqrt2w$ 取 $c=(0,\sqrt2-\lambda)$，残差 $(\lambda/\sqrt2)(u+v)$ 与 $u$ 的相关 $\lambda/\sqrt2\le\lambda$，费用 $\sqrt2\lambda-\tfrac12\lambda^2$；$x=v$ 时 $u$ 恒不活跃（残差与 $u$ 的相关为 $-c_2/\sqrt2\le0$），沿 $w$ 的一维问题在 $\lambda<1/\sqrt2$ 时取 $c_2=1/\sqrt2-\lambda$，费用 $\tfrac12-\tfrac12(1/\sqrt2-\lambda)^2=\tfrac14+\lambda/\sqrt2-\tfrac12\lambda^2$，否则 $c=0$ 费用 $\tfrac12$。逐点相减并按概率加权即得公式；两段在 $\lambda=1/\sqrt2$ 处连续。数值由代入得到。证毕。

**命题 5.5（部分吸收是通有的，repo-derived）。** 固定 $d_1=u$，令 $d_2(\alpha)=\cos\alpha\,u+\sin\alpha\,v$，$\alpha\in[\pi/4,\pi/2]$（$\alpha=\pi/4$ 为 $D_A$，$\alpha=\pi/2$ 为 $D_F$）。若 $0<\lambda<1/\sqrt2$、$p_{AB}>0$、$p_B>0$，则 $\mathcal J(\alpha)$ 在两端点附近可微且
$$
\mathcal J'(\pi/4^+)=-\,p_B\frac{1/\sqrt2-\lambda}{\sqrt2}<0,\qquad
\mathcal J'(\pi/2^-)=p_{AB}\,\lambda(1-\lambda)>0 ,
$$
故 $[\pi/4,\pi/2]$ 上的每个极小点都是内点：B 的原子严格介于 $v$ 与 $w$ 之间。

证明。$x=u$ 的费用与 $\alpha$ 无关（取 $c=(1-\lambda,0)$，残差 $\lambda u$ 与 $d_2$ 的相关 $\lambda\cos\alpha\le\lambda$）。在 $\pi/4$ 附近，$x=u+v$ 与 $x=v$ 都只用 $d_2$：对 $u+v$，取 $c_2=\cos\alpha+\sin\alpha-\lambda$，残差与 $u$ 的相关为 $1-c_2\cos\alpha$，在 $\alpha=\pi/4$ 处等于 $\lambda/\sqrt2<\lambda$，由连续性在一个邻域内 $u$ 不活跃；对 $v$，残差与 $u$ 的相关为 $-c_2\cos\alpha\le0$。单原子费用为 $\tfrac12\|x\|^2-\tfrac12(\langle x,d_2\rangle-\lambda)^2$，故该邻域内
$$
\mathcal J(\alpha)=\text{常数}-\tfrac12p_{AB}(\cos\alpha+\sin\alpha-\lambda)^2-\tfrac12p_B(\sin\alpha-\lambda)^2 ,
$$
求导并在 $\pi/4$ 代入：第一项导数含因子 $\cos\alpha-\sin\alpha=0$，第二项给 $-p_B(1/\sqrt2-\lambda)\cos(\pi/4)$。在 $\pi/2$ 附近，$x=v$ 仍只用 $d_2$，其费用 $\tfrac12-\tfrac12(\sin\alpha-\lambda)^2$ 在 $\pi/2$ 处导数为零；$x=u+v$ 两原子同时活跃：记 $g=\cos\alpha$、$m=(1-\lambda,\ \cos\alpha+\sin\alpha-\lambda)$，无约束极小 $c=(D^\top D)^{-1}m$ 在 $\alpha$ 接近 $\pi/2$ 时两坐标都接近 $1-\lambda>0$，故可行，费用为 $1-\tfrac12Q(\alpha)$，$Q=(m_1^2-2gm_1m_2+m_2^2)/(1-g^2)$。在 $\alpha=\pi/2$：$g=0$，$g'=-1$，$m_2'=-1$，分母导数为零，分子导数为 $-2g'm_1m_2+2m_2m_2'=2(1-\lambda)^2-2(1-\lambda)=-2\lambda(1-\lambda)$，故 $Q'(\pi/2)=-2\lambda(1-\lambda)$，费用导数为 $+\lambda(1-\lambda)$，乘 $p_{AB}$ 即得。两端导数符号相反，连续函数在闭区间的极小点不在端点。证毕。

**命题 5.6（单原子硬编码器下的阈值，repo-derived）。** 把约定 2.3 的目标换成每个样本最多一个活跃原子、无 $\ell_1$ 项（TopK，$K=1$）：$\operatorname{cost}_1(x;D)=\min_k\tfrac12\big(\|x\|^2-\langle x,d_k\rangle_+^2\big)$。则 $\mathcal J_1(D_A)-\mathcal J_1(D_F)=\tfrac14p_B-\tfrac12p_{AB}$：吸收字典更优当且仅当 $p_B<2p_{AB}$，与任何惩罚强度无关。

证明。$D_F$ 下 $u,v$ 费用零，$u+v$ 只能取一个原子，费用 $\tfrac12(2-1)=\tfrac12$；$D_A$ 下 $u,u+v$ 费用零，$v$ 取 $w$，费用 $\tfrac12(1-\tfrac12)=\tfrac14$。加权相减。证毕。

**评注 5.7（出现与生成，semantic）。** 引理 5.1 说 $\ell_1$ 稀疏编码在每个数据点上的最好情形是“有一个原子正对着它”，而“生成该点的方向”不是数据点。严格层级下父子共现的和 $u+v$ 本身是高频数据点，于是它赢得原子，父方向 $v$ 被吸收（定理 5.2）；共现比例下降时原子连续地转回 $v$（命题 5.5），并非跳变。这正是纤维律：重构损失的纤维（所有能精确重构的字典）对重构不可见，$\ell_1$ 在纤维内按 $\|x\|_2<\|c\|_1$ 的差额裁决。

## 6. 反例与不能推广的边界

**反例 6.1（岭误差反号时测试损失上升，repo-derived）。** 取单个测试点，$a(x)=-1$，$b(x)=1$，忽略 $E$ 项。则 $L_{\rm test}(t)=\tfrac12(-1+e^{-\lambda t})^2$ 从 $0$ 单调增到 $\tfrac12$：逃逸分量恰好补偿了岭误差，权重衰减把它冲掉后测试反而变差。纤维律只说“纤维内由 $R$ 裁决”，不说 $R$ 裁决出的点在测试上更好；后者要求真值本身落在 $R$ 偏好的那一侧（第 8 章核验取教师 $\theta^\star\in\operatorname{row}\Phi$ 正是为此）。

**反例 6.2（非线性网络不在定理 4.1–4.4 的范围内）。** 特征随训练变化的网络里 $J(\theta(t))$ 与 $K(\theta(t))$ 都在动，定理 3.4 只是逐点陈述；命题 4.7 指出线性化恰在延迟泛化的时间尺度上失效。文献里报告的无权重衰减的延迟泛化（第 7 章表所列）发生在这一范围之外，本卷对其不作断言。

**反例 6.3（两参数字典的最优不由两典型字典穷尽）。** 定理 5.4 比较的是 $D_A$ 与 $D_F$ 两点；第 8 章在 $\operatorname{span}(u,v)$ 内对两个原子的角度作网格扫描，读数显示当 $p_B/p_{AB}$ 居中时两个原子都偏离典型位置（例如 $\lambda=0.1$、$p_B/p_{AB}=0.3$ 时 argmin 在约 $(3.5^\circ,75.5^\circ)$）。因此 $\rho^\ast(\lambda)$ 是“两点之间谁更好”的阈值，不是全局最优的相变点；命题 5.5 证明了在 $d_1=u$ 的切片上最优必为内点，全局刻画留为开放问题。

**开放问题 6.4（两原子全局最优的解析刻画）。** 对 $p_B>0$，在所有单位范数二原子字典上刻画 $\arg\min\mathcal J$ 并证明最优角随 $p_B/p_{AB}$ 连续单调。缺的一步是两原子同时活跃区域内 KKT 分片的显式合并。

**开放问题 6.5（富特征区的纤维陈述）。** 在特征学习区是否存在以时变 $K(\theta(t))$ 表述的延迟泛化定理，使定理 4.4（ii）的对数平移律以某种修正形式成立。本卷未证，也未见文献给出。

**可证伪预测 6.6（预登记）。** 对固定特征的线性模型或只训练最后一层的网络，在权重衰减 $\lambda$ 下：把初始化中沿 $\ker\Phi$ 的分量放大 $s$ 倍，训练曲线逐点不变，而每个测试点进入容差的时刻恰增加 $\lambda^{-1}\log s$（定理 4.4（ii））；晚期测试损失超出量的对数斜率介于 $-2\lambda$ 与 $-\lambda$ 之间（定理 4.4（iii））。第 8 章在一个六维实例上核验了这两条；在真实的非线性网络上它们是猜想，若实测的平移与 $\lambda^{-1}\log s$ 系统偏离，按第 2.6 条视为对“线性化图景可外推”的反驳，不改本章定理。

## 7. 来源、文献状态与核验边界

**文献表态（第 3.7 条，三值之一，无“回头再说”）。**

| 来源 | 精确范围与使用边界 |
| --- | --- |
| Engl, Hanke, Neubauer, *Regularization of Inverse Problems*, Kluwer 1996, 第 5 章 Tikhonov 正则化 | `literature-attested`：定理 3.3 的极限性质；不用于任何动态陈述 |
| Jacot, Gabriel, Hongler, *Neural Tangent Kernel*, NeurIPS 2018, arXiv:1806.07572（库内条目 [jacot2018neural](../../../Library/Dynamics/jacot2018neural.md)） | `literature-attested`：命题 4.7 所用线性化的成立条件；不用于有限宽网络的定理 |
| Li, Wang, Arora, *What Happens after SGD Reaches Zero Loss? A Mathematical Framework*, ICLR 2022, arXiv:2110.06914 | `literature-attested`：零损失流形上的极限流形流形式（标签噪声 SGD 情形）；本卷定理 3.4 只用逐点陈述，不引用其极限定理 |
| Levi, Beck, Bar-Sinai, *Grokking in Linear Estimators – A Solvable Model that Groks without Understanding*, ICLR 2024, arXiv:2310.16441 | `literature-attested`：线性师生模型在权重衰减下可解的延迟泛化；定理 4.1 的分解与之同一数学对象，本卷的贡献是定理 4.3 的不可见性陈述与定理 4.4 的逃逸读数记账 |
| Lyu, Jin, Li, Du, Lee, Hu, *Dichotomy of Early and Late Phase Implicit Biases Can Provably Induce Grokking*, ICLR 2024, arXiv:2311.18817 | `literature-attested`：大初始化加小权重衰减先核区后富区的两阶段图景；本卷命题 4.7 的“线性化失效时刻”与之相容，不重证其定理 |
| Kumar, Bordelon, Gershman, Pehlevan, *Grokking as the Transition from Lazy to Rich Training Dynamics*, ICLR 2024, arXiv:2310.06110 | `literature-attested`：懒区到富区转变解释延迟泛化的经验与理论论证；用于反例 6.2 的边界 |
| Liu, Michaud, Tegmark, *Omnigrok: Grokking Beyond Algorithmic Data*, ICLR 2023, arXiv:2210.01117 | `literature-attested`：初始化范数与权重衰减控制延迟泛化的经验结论；与定理 4.4（ii）方向一致，本卷不据此声称已验证该定理 |
| Nanda, Chan, Lieberum, Smith, Steinhardt, *Progress Measures for Grokking via Mechanistic Interpretability*, ICLR 2023, arXiv:2301.05217 | `literature-attested`：白盒进度量的概念与模加法电路；命题 4.6 只借用“进度量”一词 |
| Power, Burda, Edwards, Babuschkin, Misra, *Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets*, arXiv:2201.02177 | `literature-attested`：现象的原始报告 |
| Prieto, Barsbey, Mediano, Birdal, *Grokking at the Edge of Numerical Stability*, ICLR 2025, arXiv:2501.04697；Thilak, Littwin, Zhai, Saremi, Paiss, Susskind, *The Slingshot Mechanism*, arXiv:2206.04817 | `literature-attested`：无权重衰减的延迟泛化报告；只用于反例 6.2 的边界，不用于任何正向结论 |
| Elhage 等, *Toy Models of Superposition*, Transformer Circuits Thread 2022；Bricken 等, *Towards Monosemanticity*, 2023 | `literature-attested`：叠加与稀疏自编码器的背景；本卷第 5 章不使用其任何定理 |
| Chanin, Wilken-Smith, Dulka, Bhatnagar, Golechha, Bloom, *A is for Absorption: Studying Feature Splitting and Absorption in Sparse Autoencoders*, NeurIPS 2025, arXiv:2409.14507 | `literature-attested`：特征吸收的经验报告，含“加大字典不消除吸收”；第 5 章给其一个精确玩具机制，不声称解释其全部观测 |
| Bussmann, Nabeshima, Karvonen, Nanda, *Learning Multi-Level Features with Matryoshka Sparse Autoencoders*, arXiv:2503.17547；Leask 等, *Sparse Autoencoders Do Not Find Canonical Units of Analysis*, arXiv:2502.04878 | `literature-attested`：层级特征与非规范单元的经验背景 |
| Gao 等, *Scaling and Evaluating Sparse Autoencoders*, arXiv:2406.04093；Rajamanoharan 等, *Jumping Ahead: JumpReLU SAEs*, arXiv:2407.14435 | `literature-attested`：TopK 与 JumpReLU 目标的定义；命题 5.6 只用 TopK 的定义 |
| Olshausen, Field, *Emergence of simple-cell receptive field properties by learning a sparse code for natural images*, Nature 381 (1996) | `literature-attested`：稀疏编码目标的来源 |
| — | `repo-derived`：命题 3.2；定理 3.4；定理 4.1；推论 4.2；定理 4.3；定理 4.4；命题 4.5；命题 4.6；命题 4.7 的记账部分；引理 5.1；定理 5.2；命题 5.3；定理 5.4；命题 5.5；命题 5.6；反例 6.1 |
| — | `suspected-novel`：定理 4.3 把延迟泛化的时刻写成训练曲线的逃逸集非空；引理 5.1 的等号刻画及由此得到的定理 5.2（吸收在严格层级下对任意原子数全局最优）；定理 5.4 的显式阈值 $\rho^\ast(\lambda)$；命题 5.5 的通有部分吸收；命题 5.6 的 $p_B<2p_{AB}$。检索范围：经 GPT Pro 三条检索票查 2020–2026 年 arXiv/OpenReview 与 Transformer Circuits 线程，关键词为 null space / kernel-orthogonal initialization / weight decay grokking time、feature absorption theory、dictionary learning unit-norm ℓ1 composite atoms；主循环另核对上表全部 arXiv 编号可解析。未命中只说明在此范围内未找到，不推出原创 |

**评审结论（第 5.2 条③项的落地栏）。** 评审席、票数、分歧与裁决在合并前填于此处：〔待评审〕。

**核验边界。** 第 8 章的核验覆盖：一个 $N=3,p=6$ 的整数特征矩阵与一个行空间内的教师，$\lambda=1/20$，显式 Euler 步长 $1/100$、$12000$ 步；两原子字典在 $\operatorname{span}(u,v)$ 内 $181\times181$ 角度网格、$\lambda\in\{0.1,0.3\}$、六个共现比。它证明这些实例上的等式与不等式成立到给定容差，不证明任何全称命题；定理的全称范围以第 4、5 章的证明为准。核验脚本不依赖第三方库。

## 8. 有限精确核验

脚本运行读数（macOS ARM，CPython 3.9，约 3 秒）：训练曲线成对相等到 $10^{-9}$；逃逸范数逐步等于 $(1-\lambda\,\Delta t)^k$ 倍初值到 $10^{-9}$；平台训练损失 $7.143\times10^{-3}$ 与有理精确值一致到 $10^{-8}$；测试损失在 $t\ge60$ 后与两指数形式一致到 $10^{-8}$；窗口 $[60,90]$ 的对数斜率 $-0.0986\in[-2\lambda,-\lambda]=[-0.1,-0.05]$；全部测试点符号一致的首次时刻 $t=27.42$，把逃逸分量放大 $4$ 倍后为 $55.13$，平移 $27.71$ 对预测 $\lambda^{-1}\log4=27.73$。字典部分：定理 5.4 的差额公式在 $28$ 组 $(\lambda,p)$ 上成立到 $10^{-12}$；引理 5.1 的下界在 $2000$ 个随机字典上成立；严格层级下吸收字典逐点达到下界而忠实字典严格更差。角度网格扫描的 argmin（度）如下，末列是定理 5.4 对两典型字典的预测：

| $\lambda$ | $p_B/p_{AB}$ | argmin $(\alpha_1,\alpha_2)$ | 两点比较 |
| --- | --- | --- | --- |
| 0.1 | 0 | (0, 45) | 吸收 |
| 0.1 | 0.1 | (0, 46.5) | 吸收 |
| 0.1 | 0.2 | (2.0, 67.5) | 吸收 |
| 0.1 | 0.3 | (3.5, 75.5) | 忠实 |
| 0.1 | 0.5 | (5.5, 81.5) | 忠实 |
| 0.1 | 1.0 | (18.0, 87.5) | 忠实 |
| 0.3 | 0 | (0, 45) | 吸收 |
| 0.3 | 0.1 | (0, 46) | 吸收 |
| 0.3 | 0.2 | (0, 47) | 吸收 |
| 0.3 | 0.3 | (0, 48) | 吸收 |
| 0.3 | 0.5 | (0, 50.5) | 吸收 |
| 0.3 | 1.0 | (42.5, 90) | 忠实 |

<!-- 代码块内任何行都不要以 `**` 开头：那会被子句分解器判成新子句边界。 -->

```python
# Finite exact checks for the fiber law volume. Pure python; deterministic; prints sentinel.
from fractions import Fraction as Fr
import math

# ---------- Part 1: linear model, exact rational projector, Euler flow ----------
Phi = [[1,0,1,0,0,0],[0,1,0,1,0,0],[0,0,1,1,1,0]]      # N=3 rows, p=6
N, p = len(Phi), len(Phi[0])
theta_star = [1,-1,3,1,2,0]                            # = Phi^T [1,-1,2]: teacher lies in the row space
y = [sum(Phi[i][j]*theta_star[j] for j in range(p)) for i in range(N)]
tests = [[0,1,0,0,0,1],[0,0,0,0,1,1],[1,0,0,1,0,0],[0,1,1,0,0,0]]
ytest = [sum(x[j]*theta_star[j] for j in range(p)) for x in tests]

def matmul(A,B): return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def transpose(A): return [list(r) for r in zip(*A)]
def inv(A):
    n=len(A); M=[[Fr(A[i][j]) for j in range(n)]+[Fr(int(i==j)) for j in range(n)] for i in range(n)]
    for c in range(n):
        piv=next(r for r in range(c,n) if M[r][c]!=0); M[c],M[piv]=M[piv],M[c]
        pv=M[c][c]; M[c]=[v/pv for v in M[c]]
        for r in range(n):
            if r!=c and M[r][c]!=0:
                f=M[r][c]; M[r]=[a-f*b for a,b in zip(M[r],M[c])]
    return [row[n:] for row in M]
PhiF=[[Fr(v) for v in r] for r in Phi]
G=matmul(PhiF,transpose(PhiF))                       # Phi Phi^T (3x3)
P=matmul(matmul(transpose(PhiF),inv(G)),PhiF)        # exact row-space projector (6x6)
I6=[[Fr(int(i==j)) for j in range(p)] for i in range(p)]
Pperp=[[I6[i][j]-P[i][j] for j in range(p)] for i in range(p)]
theta0=[Fr(v) for v in [3,-2,5,4,-1,6]]
def mv(A,v): return [sum(A[i][j]*v[j] for j in range(len(v))) for i in range(len(A))]
tn0=mv(Pperp,theta0); tr0=mv(P,theta0)
assert all(sum(PhiF[i][j]*tn0[j] for j in range(p))==0 for i in range(N)), "Pperp theta0 must lie in ker Phi"
vnull=tn0                                             # exact null vector, nonzero
assert any(v!=0 for v in vnull)

lam=Fr(1,20); dt=Fr(1,100); steps=12000                # t up to 120
def euler(th0):
    th=[float(v) for v in th0]; lamf=float(lam); dtf=float(dt)
    Ph=[[float(v) for v in r] for r in Phi]
    train=[]; test=[]; esc=[]
    for k in range(steps+1):
        res=[sum(Ph[i][j]*th[j] for j in range(p))-y[i] for i in range(N)]
        train.append(0.5*sum(r*r for r in res))
        test.append([sum(x[j]*th[j] for j in range(p)) for x in tests])
        esc.append(math.sqrt(sum(float(sum(Pperp[i][j]*th[j] for j in range(p)))**2 for i in range(p))))
        g=[sum(Ph[i][j]*res[i] for i in range(N))+lamf*th[j] for j in range(p)]
        th=[th[j]-dtf*g[j] for j in range(p)]
    return train,test,esc
trA,teA,escA=euler(theta0)
trB,teB,escB=euler([theta0[j]+3*vnull[j] for j in range(p)])   # same row part, different null part
# (a) identical training curves, different test curves
assert max(abs(a-b) for a,b in zip(trA,trB))<1e-9, "training curves must coincide"
assert max(abs(a-b) for ta,tb in zip(teA,teB) for a,b in zip(ta,tb))>1e-3, "test curves must differ"
# (b) escaped norm decays exactly as (1-lam*dt)^k
esc0=math.sqrt(sum(float(v)**2 for v in tn0))
assert all(abs(escA[k]-esc0*float((1-lam*dt))**k)<1e-9 for k in range(0,steps+1,500)), "escaped norm is a pure decay"
# (c) plateau training loss = lam^2/2 * ||(Phi Phi^T + lam I)^{-1} y||^2
GL=[[G[i][j]+(lam if i==j else 0) for j in range(N)] for i in range(N)]
w=mv(inv(GL),[Fr(v) for v in y]); plateau=lam*lam/2*sum(v*v for v in w)
assert abs(trA[-1]-float(plateau))<1e-8, (trA[-1],float(plateau))
# (d) exact late-phase form: prediction = ridge prediction + (1-lam*dt)^k * (escaped test component)
ridge_theta=mv(transpose(PhiF),mv(inv(GL),[Fr(v) for v in y]))          # Phi^T (Phi Phi^T + lam I)^{-1} y
a=[float(sum(Fr(x[j])*ridge_theta[j] for j in range(p))-Fr(yt)) for x,yt in zip(tests,ytest)]   # ridge error on test
b=[float(sum(Fr(x[j])*tn0[j] for j in range(p))) for x in tests]                                  # escaped initial component on test
def tl(pred): return 0.5*sum((q-yt)**2 for q,yt in zip(pred,ytest))
for k in range(6000,steps+1,1000):
    dec=float((1-lam*dt))**k
    assert abs(tl(teA[k])-0.5*sum((ai+dec*bi)**2 for ai,bi in zip(a,b)))<1e-8, k
Linf=0.5*sum(ai*ai for ai in a)
k1,k2=6000,9000
slope=(math.log(tl(teA[k2])-Linf)-math.log(tl(teA[k1])-Linf))/((k2-k1)*float(dt))
assert -2.1*float(lam)<=slope<=-0.9*float(lam), slope     # window rate lies between 2*lam (quadratic term) and lam (cross term)
sig=[float(v) for v in [G[i][i] for i in range(N)]]
# (e) sign-agreement "grokking time" shifts by log(s)/lam under scaling the escaped part
def grok_time(th0):
    tr,te,_=euler(th0)
    for k in range(steps+1):
        if all((a>0)==(b>0) for a,b in zip(te[k],ytest)): return k*float(dt)
    return None
t1=grok_time(theta0); s=4; ts=grok_time([tr0[j]+s*tn0[j] for j in range(p)])
assert t1 is not None and ts is not None and abs((ts-t1)-math.log(s)/float(lam))<0.05*math.log(s)/float(lam), (t1,ts)
print("part1 ok: t_grok(1)=%.2f t_grok(4)=%.2f predicted shift=%.2f plateau=%.3e slope=%.4f"%(t1,ts,math.log(s)/float(lam),float(plateau),slope))

# ---------- Part 2: two-atom nonnegative sparse coding in span(u,v) ----------
def nnlasso2(x,d1,d2,lam):
    """exact minimiser of 1/2||x-c1 d1-c2 d2||^2+lam(c1+c2), c>=0, unit atoms in R^2, by active sets + KKT."""
    def dot(a,b): return a[0]*b[0]+a[1]*b[1]
    best=None
    cands=[(0.0,0.0)]
    s1,s2,g=dot(x,d1),dot(x,d2),dot(d1,d2)
    if s1-lam>0: cands.append((s1-lam,0.0))
    if s2-lam>0: cands.append((0.0,s2-lam))
    det=1-g*g
    if det>1e-15:
        c1=((s1-lam)-g*(s2-lam))/det; c2=((s2-lam)-g*(s1-lam))/det
        if c1>0 and c2>0: cands.append((c1,c2))
    for c1,c2 in cands:
        r=(x[0]-c1*d1[0]-c2*d2[0],x[1]-c1*d1[1]-c2*d2[1])
        # KKT: for inactive atoms, correlation with residual <= lam
        ok=(c1>0 or dot(r,d1)<=lam+1e-12) and (c2>0 or dot(r,d2)<=lam+1e-12)
        val=0.5*dot(r,r)+lam*(c1+c2)
        if ok and (best is None or val<best[0]): best=(val,c1,c2)
    return best
u=(1.0,0.0); v=(0.0,1.0); w=(1/math.sqrt(2),1/math.sqrt(2))
def J(d1,d2,lam,pA,pAB,pB):
    return pA*nnlasso2(u,d1,d2,lam)[0]+pAB*nnlasso2((1.0,1.0),d1,d2,lam)[0]+pB*nnlasso2(v,d1,d2,lam)[0]
def delta_v(lam): return 0.25-(1-1/math.sqrt(2))*lam if lam<=1/math.sqrt(2) else 0.5-lam+lam*lam/2   # absorbed minus faithful cost on x=v
for lam_ in [0.05,0.1,0.2,0.3,0.5,0.6,0.8]:
    for (pA,pAB,pB) in [(0.3,0.5,0.0),(0.3,0.4,0.1),(0.2,0.2,0.4),(0.5,0.1,0.3)]:
        diff=J(u,w,lam_,pA,pAB,pB)-J(u,v,lam_,pA,pAB,pB)
        pred=pB*delta_v(lam_)-pAB*(lam_*(2-math.sqrt(2))-lam_*lam_/2)
        assert abs(diff-pred)<1e-12,(lam_,pA,pAB,pB,diff,pred)
# lower bound lemma: per-point cost >= lam*||x|| - lam^2/2 with equality iff an atom is aligned with x
import random
random.seed(7)
for _ in range(2000):
    a,b=random.uniform(0,2*math.pi),random.uniform(0,2*math.pi); lam_=random.uniform(0.01,0.9)
    d1=(math.cos(a),math.sin(a)); d2=(math.cos(b),math.sin(b)); x=(1.0,1.0)
    val=nnlasso2(x,d1,d2,lam_)[0]; lb=lam_*math.sqrt(2)-lam_*lam_/2
    assert val>=lb-1e-12
assert abs(nnlasso2((1.0,1.0),u,w,0.3)[0]-(0.3*math.sqrt(2)-0.045))<1e-12
# strict hierarchy: absorbed dictionary attains the per-point lower bound at every data point, faithful does not
for lam_ in [0.05,0.2,0.5,0.8]:
    assert abs(J(u,w,lam_,0.3,0.5,0.0)-(0.3*(lam_-lam_**2/2)+0.5*(lam_*math.sqrt(2)-lam_**2/2)))<1e-12
    assert J(u,v,lam_,0.3,0.5,0.0)>J(u,w,lam_,0.3,0.5,0.0)+1e-9
# report-only grid scan of the global optimum over atom angles in span(u,v)
def scan(lam_,pA,pAB,pB,n=180):
    best=None
    for i in range(n+1):
        for j in range(n+1):
            a=math.pi/2*i/n; b=math.pi/2*j/n
            if j<i: continue
            val=J((math.cos(a),math.sin(a)),(math.cos(b),math.sin(b)),lam_,pA,pAB,pB)
            if best is None or val<best[0]-1e-12: best=(val,round(math.degrees(a),1),round(math.degrees(b),1))
    return best
rows=[]
for lam_ in [0.1,0.3]:
    for ratio in [0.0,0.1,0.2,0.3,0.5,1.0]:
        pAB=0.4; pB=ratio*pAB; pA=1-0.1-pAB-pB
        thr=lam_*(2-math.sqrt(2))-lam_*lam_/2
        rows.append((lam_,ratio,scan(lam_,pA,pAB,pB),"absorbed" if pB*delta_v(lam_)<pAB*thr else "faithful"))
for r in rows: print("scan lam=%.2f pB/pAB=%.2f argmin(angles deg)=%s canonical-prediction=%s"%(r[0],r[1],r[2][1:],r[3]))
print("ALL_FINITE_CHECKS_PASSED")
```

<!-- 追加区自下一行的「追加锚」开始。每批增补写在锚之后，并以一行新的、逐字相同的追加锚结尾。 -->

## 追加锚（本行以下为增补区）
