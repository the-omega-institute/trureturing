# 白盒的纤维律：损失看不见的部分由正则项裁决

本卷研究被优化目标 $\mathcal J=L+\lambda R$ 中主损失 $L$ 的纤维：同一 $L$ 值（尤其是零集）内部的一切差别对 $L$ 不可见，纤维内的选择由正则项 $R$ 裁决。两个白盒现象作为这条律的精确实例写出：**延迟泛化**（训练损失早已平坦、测试误差很久之后才下降）是训练读数纤维坐标在权重衰减下的指数衰减，其时刻对整条训练损失曲线不可见；**特征吸收**（稀疏字典学习把父方向吸进子事件的原子）是单位原子 $\ell_1$ 稀疏编码对“出现过的点”而非“生成它的方向”的偏好。两者的共同形状是：白盒能读出纤维坐标，黑盒只能读出像。

本卷与[机器学习主卷](CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md)（下称 ML 卷）共用“读数—纤维—因子化”的语言，直接使用[《递归关系观察》](RECURSIVE_RELATIONAL_OBSERVATION.md)（下称 RRO）第 2 节的逃逸集与精确因子化定理，不重建那套框架。第 1 章定记号；第 2 章给纤维律的静态形与瞬时动态形；第 3 章在线性模型上证明泛化时刻对训练曲线的不可见性，并把已知的延迟泛化律记成本卷记号；第 4 章给稀疏字典学习的下界、严格层级下的全局吸收与部分吸收；第 5 章列反例、边界与预登记的可证伪预测；第 6 章给一个六维实例的精确读数；第 7 章逐条写文献状态。凡标 `repo-derived` 者为本卷自证，标 `literature-attested` 者以所引文献为准（本卷可重证但不冒领），标 `suspected-novel` 者只表示在第 7 章写明的检索范围内未见。

## 1. 记号与约定

**约定 1.1（读数、纤维、逃逸集与“依赖”）。** 对映射 $q:X\to Q$，其在 $z\in q[X]$ 处的纤维是 $q^{-1}(z)$。对目标 $T:X\to Y$，逃逸集按 RRO 定义 2.1 取 $\mathcal E(q;T)=\{(x,x')\in X^2:q(x)=q(x')\land T(x)\ne T(x')\}$；RRO 定理 2.2 说 $\mathcal E(q;T)=\varnothing$ 当且仅当 $T$ 经 $q$ 唯一因子化。本卷把“$T$ 对 $q$ 不可见”与“$\mathcal E(q;T)\ne\varnothing$”当作同一句话。在约定 1.2 的线性模型中，称一个以初始化 $\theta(0)$ 为自变量的量 $T$ **依赖零空间分量**，若存在 $\theta$ 与 $v\in\ker\Phi$ 使 $T(\theta)\ne T(\theta+v)$，即 $T$ 在某条固定行分量的纤维 $\{\theta+v:v\in\ker\Phi\}$ 上非常值。

**约定 1.2（线性模型）。** 特征映射 $\varphi:\mathcal X\to\mathbb R^p$；模型 $f_\theta(x)=\varphi(x)^\top\theta$。训练集 $(x_i,y_i)_{i\le N}$ 给出 $\Phi\in\mathbb R^{N\times p}$（第 $i$ 行 $\varphi(x_i)^\top$）与 $y\in\mathbb R^N$，恒设 $N\le p$ 且 $\Phi$ 行满秩，奇异值 $\sigma_1\ge\cdots\ge\sigma_N>0$。$P=\Phi^\top(\Phi\Phi^\top)^{-1}\Phi$ 是到行空间 $\operatorname{row}\Phi$ 的正交投影，$P^\perp=I-P$ 投到 $\ker\Phi$；$N=p$ 时 $P^\perp=0$，本章关于零空间分量的陈述在该情形下退化为平凡。训练损失 $L(\theta)=\tfrac12\|\Phi\theta-y\|^2$，带权重衰减的梯度流为
$$
\dot\theta=-\Phi^\top(\Phi\theta-y)-\lambda\theta,\qquad\lambda\ge0 .
$$
记 $\theta_\lambda=\Phi^\top(\Phi\Phi^\top+\lambda I)^{-1}y$（岭解），$\theta_0=\Phi^\top(\Phi\Phi^\top)^{-1}y$（最小范数插值解）。对测试点 $x$ 与其目标 $y(x)$ 记 $a(x)=\varphi(x)^\top\theta_\lambda-y(x)$（岭误差）与 $b(x)=\varphi(x)^\top P^\perp\theta(0)$（初始化逃逸到 $\ker\Phi$ 的分量在 $x$ 处的读数）；对有限测试集把它们写成向量 $a,b$，$\langle a,b\rangle=\sum_xa(x)b(x)$。

**约定 1.3（字典学习）。** 数据 $x$ 取自 $\mathbb R^d$ 上有限支撑的分布。字典 $D=[d_1,\dots,d_K]$，各原子单位范数 $\|d_k\|_2=1$；码 $c\in\mathbb R^K_{\ge0}$。两阶段目标
$$
\operatorname{cost}(x;D)=\min_{c\ge0}\Big[\tfrac12\|x-Dc\|_2^2+\lambda\|c\|_1\Big],\qquad
\mathcal J(D)=\mathbb E_x\operatorname{cost}(x;D),\qquad 0<\lambda<1 .
$$
这是稀疏自编码器目标去掉摊销编码器后的内层精确形式；摊销编码器只能使目标更大，故本卷结论是对理想编码器的结论。取 $u,v$ 为标准正交单位向量，$w=(u+v)/\sqrt2$；数据支撑于 $\{0,u,u+v,v\}$，概率 $p_0,p_A,p_{AB},p_B$。约定 $u$ 是父特征 A 的方向、$v$ 是子特征 B 的方向，$p_B$ 是“B 单独出现”的概率，$p_B=0$ 称严格层级（B 蕴含 A）。两个典型字典：忠实字典 $D_F=[u,v]$ 与吸收字典 $D_A=[u,w]$。

## 2. 读数纤维与正则裁决

**定义 2.1（切向逃逸空间）。** 设 $F:\mathbb R^p\to\mathbb R^N$ 连续可微，$L(\theta)=\tfrac12\|F(\theta)-y\|^2$，零集 $Z=F^{-1}(y)$。对 $\theta\in Z$，令 $J=DF(\theta)$，切向逃逸空间 $K(\theta)=\ker J$。当 $F\in C^1$ 且 $J$ 在 $\theta$ 的邻域上秩恒定时 $Z$ 在 $\theta$ 附近是 $C^1$ 子流形且 $T_\theta Z=K(\theta)$；不满足秩恒定时 $K(\theta)$ 仍有定义，但不必是 $Z$ 的切空间（例如 $F(z)=z^2$、$y=0$、$\theta=0$ 有 $K(0)=\mathbb R$ 而 $Z=\{0\}$）。

**命题 2.2（损失对切向逃逸三阶盲，repo-derived）。** 设 $F$ 二次连续可微，$\theta\in Z$，$v\in K(\theta)$。则 $\ell(\varepsilon)=L(\theta+\varepsilon v)$ 在 $\varepsilon=0$ 处的一、二、三阶导数全为零，且 $\ell(\varepsilon)=O(\varepsilon^4)$。

证明。令 $g(\varepsilon)=F(\theta+\varepsilon v)-y$。$g(0)=0$、$g'(0)=Jv=0$，$g$ 二次连续可微，故 $g(\varepsilon)=O(\varepsilon^2)$、$g'(\varepsilon)=O(\varepsilon)$、$g''$ 有界。于是 $\ell=\tfrac12\|g\|^2=O(\varepsilon^4)$，$\ell'=\langle g,g'\rangle=O(\varepsilon^3)$，$\ell''=\|g'\|^2+\langle g,g''\rangle=O(\varepsilon^2)$；三者在 $0$ 处为零，且 $\ell''(\varepsilon)=O(\varepsilon^2)$ 给 $\ell'''(0)=0$。证毕。

**定理 2.3（零集上的静态裁决，literature-attested：Tikhonov 正则化极限）。** 设 $\Theta$ 紧，$L,R:\Theta\to\mathbb R$ 连续，$\Theta_0=\arg\min L\ne\varnothing$。取 $\lambda_k\downarrow0$（$\lambda_k>0$）与 $\theta_k\in\arg\min(L+\lambda_kR)$。则 $(\theta_k)$ 的任一极限点 $\bar\theta$ 满足 $\bar\theta\in\arg\min_{\Theta_0}R$。

证明。取 $\theta^\star\in\arg\min_{\Theta_0}R$，$L^\star=\min L$。由 $\theta_k$ 的最优性，$L(\theta_k)+\lambda_kR(\theta_k)\le L^\star+\lambda_kR(\theta^\star)$。因 $L(\theta_k)\ge L^\star$，得 $R(\theta_k)\le R(\theta^\star)$；又 $R$ 在紧集上有界，得 $L(\theta_k)\le L^\star+\lambda_k(R(\theta^\star)-R(\theta_k))\to L^\star$。沿子列取极限并用连续性：$L(\bar\theta)=L^\star$ 且 $R(\bar\theta)\le R(\theta^\star)$。这是 Tikhonov 正则化的经典极限性质（第 7 章表），本卷重证以固定记号。证毕。

**定理 2.4（零集上的瞬时动态裁决，repo-derived）。** 设 $R$ 可微，$\theta\in Z$，考虑流 $\dot\theta=-\nabla L(\theta)-\lambda\nabla R(\theta)$。则在 $\theta$ 处 $\dot\theta=-\lambda\nabla R(\theta)$，按 $K(\theta)\oplus K(\theta)^\perp$ 分解为 $-\lambda P_{K(\theta)}\nabla R(\theta)$ 与 $-\lambda P_{K(\theta)^\perp}\nabla R(\theta)$；在定义 2.1 的秩恒定条件下前者是沿 $Z$ 的切向分量、后者是法向分量。此时 $\frac{d}{dt}L(\theta(t))=0$。取 $R=\tfrac12\|\theta\|^2$ 时切向分量为 $-\lambda P_{K(\theta)}\theta$。

证明。$\theta\in Z$ 给 $\nabla L(\theta)=J^\top(F(\theta)-y)=0$，故速度只剩正则项；正交分解与 $\frac{d}{dt}L=\langle\nabla L,\dot\theta\rangle=0$ 都是直接计算。这是一个逐点陈述：$Z$ 在带权重衰减的流下一般不是不变集，离开 $Z$ 之后 $\nabla L$ 重新出现，长期行为要靠具体模型（第 3 章在线性模型上用其精确解；在光滑吸引的插值流形与 Morse–Bott 条件下，$\lambda\to0$ 的慢时间极限流 $d\bar\theta/d\tau=-P_{T\bar\theta Z}\bar\theta$ 是文献定理，第 7 章标注，本卷不重证）。证毕。

**评注 2.5（纤维律，semantic）。** 定理 2.3 与 2.4 是同一句话的静态形与动态形：主损失 $L$ 以其像为读数，纤维内部对它不可见；在纤维内挑选的是 $R$。精确的纤维图景属于约束问题或 $\lambda\to0^+$ 极限；有限 $\lambda$ 下最优解一般不在 $L$ 的零集上，比较必须同时计入 $L$ 与 $R$ 的变化（第 3 章的平台值与第 4 章的费用表都是这样的完整比较）。白盒解释的对象恰是纤维坐标——它们可从参数直接读出。它们是否也不出现在损失曲线里，取决于正则项是否把纤维坐标耦合回 $L$ 的方向：第 3 章的线性模型加各向同性权重衰减满足这一点（定理 3.1（i）），而一般情形不然——取 $L(x,z)=x^2/2$、$R(x,z)=(x-z)^2/2$、$\lambda=1$，初始化 $(0,0)$ 与 $(0,1)$ 同在零集，前者不动，后者有 $\dot x(0)=1$，故 $L(\theta(t))=t^2/2+O(t^3)$，损失曲线分得开这两个纤维坐标。

## 3. 线性模型：训练读数的纤维

本章只有一条新命题——泛化时刻对整条训练损失曲线不可见——其余内容是已知的延迟泛化律在本卷记号下的记账，逐条标注先例（第 7 章表），不单列为定理。

**定理 3.1（成对实例：泛化时刻对训练曲线不可见，repo-derived）。** 在约定 1.2 下设 $\lambda\ge0$，$v\in\ker\Phi$，$v\ne0$。
（i）初始化 $\theta(0)$ 与 $\theta(0)+v$ 的训练损失曲线在所有 $t\ge0$ 逐点相等；
（ii）它们在任一满足 $\varphi(x)^\top v\ne0$ 的测试点上的预测相差 $e^{-\lambda t}\varphi(x)^\top v$；
（iii）以整条训练曲线 $q:\theta(0)\mapsto(t\mapsto L(\theta(t)))$ 为读数，任何依赖零空间分量（约定 1.1）的量 $T$ 都有 $\mathcal E(q;T)\ne\varnothing$，故按 RRO 定理 2.2 不存在把 $T$ 表成训练曲线之函数的方式；
（iv）“某测试点的预测误差首次不超过容差 $\varepsilon$ 的时刻”是这样的量：取 $N=1,p=2$，$\Phi=(1,0)$，$y=0$，$\lambda>0$，测试特征 $\varphi(x)=e_2$、目标 $y(x)=0$，$0<\varepsilon<1$，初始化 $(0,1)$ 与 $(0,2)$。两者训练曲线恒为零，而进入时刻分别为 $\lambda^{-1}\log(1/\varepsilon)$ 与 $\lambda^{-1}\log(2/\varepsilon)$。

证明。中间步骤是正则最小二乘梯度流的已知精确解（第 7 章表：Hoerl–Kennard 的岭代数，Levi–Beck–Bar-Sinai、Boursier–Pesme–Dragomir 与 Xu–Vardi–Safran 的零空间分量衰减），这里只作一行验证：$\Phi^\top(\Phi\theta-y)\in\operatorname{row}\Phi$ 给 $P^\perp\dot\theta=-\lambda P^\perp\theta$，故 $P^\perp\theta(t)=e^{-\lambda t}P^\perp\theta(0)$；行分量满足 $\dot\theta_r=-(\Phi^\top\Phi+\lambda I)\theta_r+\Phi^\top y$，其不动点 $(\Phi^\top\Phi+\lambda I)^{-1}\Phi^\top y=\theta_\lambda$（推移恒等式），故
$$
\theta(t)=\theta_\lambda+e^{-(\Phi^\top\Phi+\lambda I)t}\big(P\theta(0)-\theta_\lambda\big)+e^{-\lambda t}P^\perp\theta(0),
$$
$\Phi^\top\Phi+\lambda I$ 限制到 $\operatorname{row}\Phi$ 的谱为 $\{\sigma_i^2+\lambda\}$，$\lambda=0$ 时把 $\theta_\lambda$ 读作 $\theta_0$。（i）$P(\theta(0)+v)=P\theta(0)$，两条轨迹的行分量逐点相等，而 $\Phi\theta=\Phi\theta_r$，故训练残差相等。（ii）零空间分量相差 $e^{-\lambda t}v$，作用到 $\varphi(x)$ 即得。（iii）依赖零空间分量的定义恰给出一对 $\theta,\theta+v$ 使 $T$ 取不同值，而由（i）它们的 $q$ 相同，故这一对属于 $\mathcal E(q;T)$；RRO 定理 2.2 给结论。（iv）$\ker\Phi=\operatorname{span}(e_2)$，两初始化的行分量都是零且 $y=0$，训练残差恒为零；预测分别为 $e^{-\lambda t}$ 与 $2e^{-\lambda t}$，进入时刻由 $e^{-\lambda t}=\varepsilon$、$2e^{-\lambda t}=\varepsilon$ 解出。仅预测不同不足以推出任意统计量不同（对称的容差统计量在 $\pm b$ 上相等），所以（iii）的“依赖”按约定 1.1 取非常值，（iv）给出实际见证。证毕。

**评注 3.2（逃逸读数的记账，semantic；所记均为已知律）。** 记 $s(t)=e^{-\lambda t}$，$E(t)=e^{-(\Phi^\top\Phi+\lambda I)t}(P\theta(0)-\theta_\lambda)$。由定理 3.1 证明中的精确解，对任意测试点 $f_{\theta(t)}(x)-y(x)=a(x)+s(t)b(x)+\varphi(x)^\top E(t)$，$\|E(t)\|\le e^{-(\sigma_N^2+\lambda)t}\|P\theta(0)-\theta_\lambda\|$；训练损失只依赖 $P\theta(0)$，平台值 $L_\infty=\tfrac{\lambda^2}{2}\|(\Phi\Phi^\top+\lambda I)^{-1}y\|^2\le\lambda^2\|y\|^2/(2(\sigma_N^2+\lambda)^2)$（岭残差 $\Phi\theta_\lambda-y=-\lambda(\Phi\Phi^\top+\lambda I)^{-1}y$），收敛速率不慢于 $\sigma_N^2+\lambda$。对有限测试集，归约曲线 $\widetilde L(s)=\tfrac12\|a\|^2+s\langle a,b\rangle+\tfrac12s^2\|b\|^2$ 与实际测试损失之差 $\rho(t)$ 满足 $|\rho(t)|\le\|E(t)\|\sum_x|a(x)+s(t)b(x)|\,\|\varphi(x)\|+\tfrac12\|E(t)\|^2\sum_x\|\varphi(x)\|^2$，其衰减率下界 $\sigma_N^2+\lambda$ 恒大于 $\lambda$、与 $2\lambda$ 的大小关系不由假设决定。设 $\lambda>0$：逃逸读数 $|s(t)b(x)|$ 首次不超过 $\varepsilon$ 的时刻为 $T_\varepsilon(x)=\max\{0,\lambda^{-1}\log(|b(x)|/\varepsilon)\}$，把 $P^\perp\theta(0)$ 换成 $sP^\perp\theta(0)$（$s>1$）而不动 $P\theta(0)$ 时每个 $T_\varepsilon(x)>0$ 恰增加 $\lambda^{-1}\log s$ 而训练曲线不变（Omnigrok 的对数时钟启发式、Xu–Vardi–Safran 式 (8)、Kim §7.4）；当 $b\ne0$、$\langle a,b\rangle\ge0$ 时归约超出量 $g(s)=s\langle a,b\rangle+\tfrac12s^2\|b\|^2>0$，$\frac{d}{dt}\log g=-\lambda\,\frac{\langle a,b\rangle+s\|b\|^2}{\langle a,b\rangle+\frac12s\|b\|^2}\in[-2\lambda,-\lambda]$，渐近速率在 $\langle a,b\rangle>0$ 时为 $\lambda$、为零时为 $2\lambda$（Kim 定理 20 的单根/双根二分），$\langle a,b\rangle<0$ 时 $g$ 在 $s=-2\langle a,b\rangle/\|b\|^2$ 变号（该根落在 $(0,1]$ 内才在 $t\ge0$ 上发生）；解中只有两类速率，行模态的 $\sigma_i^2+\lambda$ 与零空间模态的 $\lambda$，最慢行模态与零空间模态之比为 $1+\sigma_N^2/\lambda$，本卷不假设它大。$\lambda>0$、$P^\perp\theta(0)\ne0$ 时 $\|P^\perp\theta(t)\|=e^{-\lambda t}\|P^\perp\theta(0)\|$ 可由参数直接算出、严格递减、对数线性，而按定理 3.1（i）它对训练损失曲线不可见——这就是白盒能读、黑盒读不到的那个坐标。

**评注 3.3（无正则项时没有独立的慢模态，semantic）。** $\lambda=0$ 时 $P^\perp\theta(t)\equiv P^\perp\theta(0)$，且 $|f_{\theta(t)}(x)-\varphi(x)^\top\theta_0-b(x)|\le\|\varphi(x)\|e^{-\sigma_N^2t}\|P\theta(0)-\theta_0\|$：测试预测与其极限之差只含训练瞬态的速率，不存在由零空间分量单独贡献的慢衰减模态。这不排除进入某容差的时刻可以任意晚：沿一个读到非零瞬态的固定方向放大 $\varphi(x)$，同一瞬态跨过同一容差就越晚（$\Phi=(1,0)$、$y=0$、$\theta(0)=(1,0)$、$\varphi(x)=(M,0)$、$y(x)=0$ 时训练损失 $\tfrac12e^{-2t}$、测试损失 $\tfrac12M^2e^{-2t}$）；慢的行模态也能造成晚期改善：$\Phi=\operatorname{diag}(1,\delta)$、$y=(1,\delta)$、$\theta(0)=0$、$0<\delta^2\le\tfrac14$ 时 $\theta(t)=(1-e^{-t},1-e^{-\delta^2t})$，训练损失 $\tfrac12e^{-2t}+\tfrac12\delta^2e^{-2\delta^2t}$，而测试点 $\varphi(x)=(-\tfrac12,1)$（目标 $\tfrac12$）的预测 $g(t)=\tfrac12+\tfrac12e^{-t}-e^{-\delta^2t}$ 从 $g(0)=0$ 先降后升，恰有一个正根 $t_\delta$，满足 $e^{-\delta^2t_\delta}=\tfrac12(1+e^{-t_\delta})$；由 $g(1)<0$ 得 $t_\delta>1$，故 $\delta^{-2}\log\frac{2}{1+e^{-1}}\le t_\delta\le\delta^{-2}\log2$，随 $\delta\to0$ 趋于无穷。Levi–Beck–Bar-Sinai 式 (12) 的无权重衰减延迟是这种慢行模态的高维实例。

**评注 3.4（线性化网络中的记账，semantic）。** 对可微网络在其初始化点 $\theta_0=\theta(0)$ 处线性化 $f_\theta(x)\approx f_{\theta_0}(x)+\varphi(x)^\top(\theta-\theta_0)$，$\varphi(x)=\nabla_\theta f_\theta(x)|_{\theta_0}$，并对 $\theta$ 施加权重衰减，记 $\delta=\theta-\theta_0$、$\delta_r$ 为其行空间分量，则线性化模型内的测试预测为 $f_{\theta_0}(x)-\varphi(x)^\top P^\perp\theta_0+\varphi(x)^\top\delta_r(t)+e^{-\lambda t}\varphi(x)^\top P^\perp\theta_0$（零空间分量满足 $\dot\delta_n=-\lambda(\delta_n+P^\perp\theta_0)$、$\delta_n(0)=0$，解 $\delta_n(t)=-(1-e^{-\lambda t})P^\perp\theta_0$；线性化点异于初始化时 $\delta_n(t)=-P^\perp\theta_0+e^{-\lambda t}P^\perp\theta(0)$），$\delta_r(t)$ 以不慢于 $e^{-(\sigma_N^2+\lambda)t}$ 的速率收敛到常向量，故忽略这一瞬态后只有末项随时间变化；常数 $f_{\theta_0}(x)-\varphi(x)^\top P^\perp\theta_0$ 在线性化模型内永不衰减（对一次齐次网络它等于 $\varphi(x)^\top P\theta_0$，落在训练可见的行空间读数内）。沿零空间的参数位移 $\|\delta_n(t)\|=(1-e^{-\lambda t})\|P^\perp\theta_0\|$ 在 $c\le\lambda t\le C$（$0<c\le C$ 固定）时落在 $\|P^\perp\theta_0\|$ 的固定正比例区间 $[1-e^{-c},1-e^{-C}]$ 内。本卷不给出线性化余项的任何界，因此不断言线性化在何时失效；对非线性网络本章只是这一层记账（线性化的定义与无限宽条件见第 7 章表 Jacot 行）。

## 4. 稀疏字典学习中的吸收

**引理 4.1（单点下界与对齐等式，literature-attested：欧氏范数的近端收缩与三角不等式取等；本卷重证并加字典级刻画）。** 在约定 1.3 下，对任意 $x\ne0$、任意单位范数字典 $D$ 与 $0<\lambda<\|x\|$，
$$
\operatorname{cost}(x;D)\ \ge\ \lambda\|x\|-\tfrac12\lambda^2 ,
$$
等号成立当且仅当 $D$ 含原子 $x/\|x\|$；此时可取最优码把 $\|x\|-\lambda$ 放在该原子上、其余为零（若该原子重复出现，任一非负拆分同样最优）。

证明。对任意 $c\ge0$ 记 $r=\|x-Dc\|$。三角不等式与单位范数给 $\|x\|\le\|Dc\|+r\le\sum_kc_k\|d_k\|+r=\|c\|_1+r$，故目标 $\ge\tfrac12r^2+\lambda(\|x\|-r)\ge\lambda\|x\|-\tfrac12\lambda^2$，后一步在 $r=\lambda$ 取最小。等号要求 $\|Dc\|=\|c\|_1$（所有活跃原子相同）、$r=\lambda$ 且 $x-Dc$ 与 $Dc$ 同向（三角不等式取等），即 $Dc=(\|x\|-\lambda)x/\|x\|$，活跃原子只能是 $x/\|x\|$。反之若该原子在字典里，取该码即达下界；$\lambda>0$ 给强制性，有限字典上最小值可达。证毕。

**定理 4.2（严格层级下吸收全局最优，literature-attested 的二原子先例见第 7 章；本卷对任意原子数重证）。** 数据支撑于 $\{0,u,u+v\}$，$p_A,p_{AB}>0$，$0<\lambda<1$。则在所有单位范数字典（任意原子数）上
$$
\min_D\mathcal J(D)=p_A\big(\lambda-\tfrac12\lambda^2\big)+p_{AB}\big(\sqrt2\lambda-\tfrac12\lambda^2\big),
$$
极小点集恰为同时含原子 $u$ 与 $w$ 的字典；在每个极小点上 $x=u+v$ 的最优码只落在与 $w$ 相等的原子上。忠实字典 $D_F=[u,v]$ 严格次优，差额恰为 $p_{AB}\lambda(2-\sqrt2-\lambda/2)>0$。

证明。对每个数据点用引理 4.1：$\|u\|=1$、$\|u+v\|=\sqrt2$，下界之和即右端，等号当且仅当两原子都在，且等号情形的码只用对齐原子。对 $D_F$，原子正交，$\operatorname{cost}(u+v;D_F)=\min_{c\ge0}\tfrac12[(1-c_1)^2+(1-c_2)^2]+\lambda(c_1+c_2)$ 按坐标分离，各在 $1-\lambda$ 取到 $\lambda-\tfrac12\lambda^2$，合计 $2\lambda-\lambda^2$；减去 $\sqrt2\lambda-\tfrac12\lambda^2$ 得 $\lambda(2-\sqrt2-\lambda/2)$，因 $2-\sqrt2>\tfrac12$ 而对 $\lambda<1$ 为正。证毕。

**命题 4.3（深度 $m$ 的层级，repo-derived）。** 设 $x=u_1+\cdots+u_m$，$u_i$ 标准正交，$m\ge2$，$0<\lambda<1$。以 $x/\sqrt m$ 为原子的费用为 $\sqrt m\lambda-\tfrac12\lambda^2$；以 $u_1,\dots,u_m$ 为原子分解 $x$ 的费用为 $m(\lambda-\tfrac12\lambda^2)$；二者之差 $\lambda(m-\sqrt m)-\tfrac12(m-1)\lambda^2$ 对 $\lambda<1$ 恒正。

证明。前者由引理 4.1 的等号情形；后者按坐标分离同定理 4.2。差为正当且仅当 $\lambda<2(m-\sqrt m)/(m-1)=2\sqrt m/(\sqrt m+1)$，而右端对 $m\ge2$ 大于 $1$。证毕。

**定理 4.4（两典型字典的精确比较，repo-derived）。** 在约定 1.3 的四点支撑上，对 $0<\lambda<1$，
$$
\mathcal J(D_A)-\mathcal J(D_F)=p_B\,\Delta_v(\lambda)-p_{AB}\,\lambda\Big(2-\sqrt2-\frac\lambda2\Big),\qquad
\Delta_v(\lambda)=\begin{cases}\tfrac14-\big(1-\tfrac1{\sqrt2}\big)\lambda,&\lambda\le\tfrac1{\sqrt2},\\[2pt]\tfrac12-\lambda+\tfrac12\lambda^2,&\tfrac1{\sqrt2}\le\lambda<1.\end{cases}
$$
故当 $p_{AB}>0$ 时，在两者之间吸收字典更优当且仅当 $p_B/p_{AB}<\rho^\ast(\lambda)=\lambda(2-\sqrt2-\lambda/2)/\Delta_v(\lambda)$；$\rho^\ast(0.1)\approx0.2428$，$\rho^\ast(0.3)\approx0.8064$。

证明。目标关于 $c\ge0$ 严格凸，KKT 条件充分：活跃原子的相关 $\langle x-Dc,d_k\rangle=\lambda$，非活跃原子的相关 $\le\lambda$。$D_F$ 下三点费用分别为 $\lambda-\tfrac12\lambda^2$（$u$）、$2\lambda-\lambda^2$（$u+v$）、$\lambda-\tfrac12\lambda^2$（$v$）。$D_A=[u,w]$ 下：$x=u$ 取 $c=(1-\lambda,0)$，残差 $\lambda u$ 与 $w$ 的相关 $\lambda/\sqrt2\le\lambda$，费用 $\lambda-\tfrac12\lambda^2$；$x=u+v=\sqrt2w$ 取 $c=(0,\sqrt2-\lambda)$，残差 $(\lambda/\sqrt2)(u+v)$ 与 $u$ 的相关 $\lambda/\sqrt2\le\lambda$，费用 $\sqrt2\lambda-\tfrac12\lambda^2$；$x=v$ 时 $u$ 恒不活跃（残差与 $u$ 的相关为 $-c_2/\sqrt2\le0$），沿 $w$ 的一维问题在 $\lambda<1/\sqrt2$ 时取 $c_2=1/\sqrt2-\lambda$，费用 $\tfrac12-\tfrac12(1/\sqrt2-\lambda)^2=\tfrac14+\lambda/\sqrt2-\tfrac12\lambda^2$，否则 $c=0$ 费用 $\tfrac12$。逐点相减并按概率加权即得公式；两段在 $\lambda=1/\sqrt2$ 处连续。数值由代入得到。证毕。

**命题 4.5（部分吸收是通有的，repo-derived）。** 固定 $d_1=u$，令 $d_2(\alpha)=\cos\alpha\,u+\sin\alpha\,v$，$\alpha\in[\pi/4,\pi/2]$（$\alpha=\pi/4$ 为 $D_A$，$\alpha=\pi/2$ 为 $D_F$）。若 $0<\lambda<1/\sqrt2$、$p_{AB}>0$、$p_B>0$，则 $\mathcal J(\alpha)$ 在两端点附近可微且
$$
\mathcal J'(\pi/4^+)=-\,p_B\frac{1/\sqrt2-\lambda}{\sqrt2}<0,\qquad
\mathcal J'(\pi/2^-)=p_{AB}\,\lambda(1-\lambda)>0 ,
$$
故 $[\pi/4,\pi/2]$ 上的每个极小点都是内点：子事件的原子严格介于 $v$ 与 $w$ 之间。本命题不断言极小点唯一，也不断言它随 $p_B/p_{AB}$ 连续或单调变化。

证明。$x=u$ 的费用与 $\alpha$ 无关（取 $c=(1-\lambda,0)$，残差 $\lambda u$ 与 $d_2$ 的相关 $\lambda\cos\alpha\le\lambda$）。在 $\pi/4$ 附近，$x=u+v$ 与 $x=v$ 都只用 $d_2$：对 $u+v$，取 $c_2=\cos\alpha+\sin\alpha-\lambda$，残差与 $u$ 的相关为 $1-c_2\cos\alpha$，在 $\alpha=\pi/4$ 处等于 $\lambda/\sqrt2<\lambda$，由连续性在一个邻域内 $u$ 不活跃；对 $v$，残差与 $u$ 的相关为 $-c_2\cos\alpha\le0$。单原子费用为 $\tfrac12\|x\|^2-\tfrac12(\langle x,d_2\rangle-\lambda)^2$，故该邻域内
$$
\mathcal J(\alpha)=\text{常数}-\tfrac12p_{AB}(\cos\alpha+\sin\alpha-\lambda)^2-\tfrac12p_B(\sin\alpha-\lambda)^2 ,
$$
求导并在 $\pi/4$ 代入：第一项导数含因子 $\cos\alpha-\sin\alpha=0$，第二项给 $-p_B(1/\sqrt2-\lambda)\cos(\pi/4)$。在 $\pi/2$ 附近，$x=v$ 仍只用 $d_2$，其费用 $\tfrac12-\tfrac12(\sin\alpha-\lambda)^2$ 在 $\pi/2$ 处导数为零；$x=u+v$ 两原子同时活跃：记 $g=\cos\alpha$、$m=(1-\lambda,\ \cos\alpha+\sin\alpha-\lambda)$，无约束极小 $c=(D^\top D)^{-1}m$ 在 $\alpha$ 接近 $\pi/2$ 时两坐标都接近 $1-\lambda>0$，故可行，费用为 $1-\tfrac12Q(\alpha)$，$Q=(m_1^2-2gm_1m_2+m_2^2)/(1-g^2)$。在 $\alpha=\pi/2$：$g=0$，$g'=-1$，$m_2'=-1$，分母导数为零，分子导数为 $-2g'm_1m_2+2m_2m_2'=2(1-\lambda)^2-2(1-\lambda)=-2\lambda(1-\lambda)$，故 $Q'(\pi/2)=-2\lambda(1-\lambda)$，费用导数为 $+\lambda(1-\lambda)$，乘 $p_{AB}$ 即得。两端导数符号相反，连续函数在闭区间的极小点不在端点。证毕。

**命题 4.6（单原子硬编码器下的阈值，repo-derived）。** 把约定 1.3 的目标换成每个样本最多一个活跃原子、无 $\ell_1$ 项（TopK，$K=1$，理想编码器）：$\operatorname{cost}_1(x;D)=\min_k\tfrac12\big(\|x\|^2-\langle x,d_k\rangle_+^2\big)$。则 $\mathcal J_1(D_A)-\mathcal J_1(D_F)=\tfrac14p_B-\tfrac12p_{AB}$：吸收字典更优当且仅当 $p_B<2p_{AB}$，与任何惩罚强度无关。

证明。$D_F$ 下 $u,v$ 费用零，$u+v$ 只能取一个原子，费用 $\tfrac12(2-1)=\tfrac12$；$D_A$ 下 $u,u+v$ 费用零，$v$ 取 $w$，费用 $\tfrac12(1-\tfrac12)=\tfrac14$。加权相减。证毕。

**命题 4.7（原子在场不等于码可组合，repo-derived）。** 在约定 1.3 的四点支撑上取 $p_A,p_{AB},p_B>0$，三原子字典 $D_3=[u,v,w]$，$0<\lambda<1$。则 $D_3$ 在所有单位范数字典上全局最优，且其最优码把 $x=u+v$ 完全放在 $w$ 上，$u$ 与 $v$ 的码为零：忠实原子 $u,v$ 都在字典里，但共现事件从不同时激活它们。

证明。三个非零数据点 $u,v,u+v$ 的方向 $u,v,w$ 都是 $D_3$ 的原子，引理 4.1 的下界逐点取等，故 $\mathcal J(D_3)$ 等于三点下界的加权和，是全局最小值；等号情形的码只用对齐原子，$x=u+v$ 的最优码只在 $w$ 上。证毕。

**评注 4.8（出现与生成，semantic）。** 引理 4.1 说单位原子 $\ell_1$ 稀疏编码在每个数据点上的最好情形是“有一个原子正对着它”，而“生成该点的方向”本身不是数据点。严格层级下父子共现的和 $u+v$ 是正概率数据点，于是它赢得原子：父方向 $u$ 被吸进子事件的原子 $w$；在 $p_A,p_{AB}>0$、$p_B=0$ 的二原子极小点上子方向 $v$ 本身没有原子（$p_A=0$ 时 $[v,w]$ 也是极小点；定理 4.2 允许更多原子，例如 $[u,v,w]$ 也是极小点，只是 $v$ 不参与共现事件的编码）。当 $p_{AB},p_B>0$ 且 $0<\lambda<1/\sqrt2$ 时两个典型字典都不是切片上的极小点（命题 4.5），最优原子落在中间（$\lambda\ge1/\sqrt2$ 时不然：例如 $\lambda=0.8$ 时 $x=v$ 在 $\alpha=\pi/4$ 附近码为零，$\mathcal J'(\pi/4)=0$、$\mathcal J''(\pi/4^+)=p_{AB}\sqrt2(\sqrt2-\lambda)>0$，吸收端点是切片上的严格局部极小），至于它怎样随 $p_B/p_{AB}$ 移动本卷未证（开放问题 5.6）。这是纤维律在有限 $\lambda$ 下的形态：在 $\lambda\to0^+$ 的约束极限里，所有精确重构的字典构成重构损失的纤维，$\ell_1$ 在其中按 $\|x\|_2<\|c\|_1$ 的差额裁决（定理 2.3）；在有限 $\lambda$ 下最优码不再精确重构（$D_A$ 与 $D_F$ 在 $u+v$ 上的重构损失分别为 $\lambda^2/2$ 与 $\lambda^2$），定理 4.4 计入的是两项之和。

## 5. 反例、边界与预登记的预测

**反例 5.1（岭误差反号时测试损失上升，repo-derived）。** 取 $\lambda>0$、单个测试点、$a(x)=-1$、$b(x)=1$，只看归约曲线（$E=0$ 可精确实现：$\Phi=(1,0)$、$y=0$、$\theta(0)=(0,1)$、$\varphi(x)=e_2$、$y(x)=1$）。则 $\widetilde L(s(t))=\tfrac12(-1+e^{-\lambda t})^2$ 从 $0$ 严格增到 $\tfrac12$，导数为 $\lambda e^{-\lambda t}(1-e^{-\lambda t})$：逃逸分量恰好补偿了岭误差，权重衰减把它冲掉后测试反而变差。纤维律只说“纤维内由 $R$ 裁决”，不说 $R$ 裁决出的点在测试上更好；后者要求真值本身落在 $R$ 偏好的那一侧（第 6 章的实例取教师 $\theta^\star\in\operatorname{row}\Phi$ 正是为此）。

**反例 5.2（非线性网络不在定理 3.1 与评注 3.2 的范围内）。** 特征随训练变化的网络里 $J(\theta(t))$ 随时间变化，$K(\theta(t))$ 也可能变化，定理 2.4 只是逐点陈述，评注 3.4 只是线性化模型内的记账并且不给失效时刻。文献报告的特征学习或自适应优化器下无权重衰减的延迟泛化（第 7 章表所列非线性网络的结果）发生在这一范围之外，本卷对其不作断言；线性模型中无权重衰减的晚期改善由评注 3.3 的慢行模态解释。

**反例 5.3（两参数字典的最优不由两典型字典穷尽）。** 定理 4.4 比较的是 $D_A$ 与 $D_F$ 两点，而命题 4.5 证明当 $p_{AB},p_B>0$、$0<\lambda<1/\sqrt2$ 时在 $d_1=u$ 的切片上两端点都不是极小点，故存在严格优于二者的字典。因此 $\rho^\ast(\lambda)$ 只是“两点之间谁更好”的阈值，不是全局最优的相变点；两个原子同时自由时的极小点（包括 $d_1$ 是否离开 $u$）留为开放问题 5.6。

**反例 5.4（解码器偏置改变几何）。** 若目标改为重构 $x-b$（带解码器偏置 $b$），取 $p_0=p_B=0$ 并固定 $b=u$，则数据 $\{u,u+v\}$ 变成残差 $\{0,v\}$，一个 $v$ 原子即足，父方向由偏置承担：定理 4.2 的吸收在这个固定偏置的问题里不出现。这是另一个问题，不是对定理 4.2 的反驳；自由优化的偏置是否取 $u$，本卷未证。

**反例 5.5（幅值可变时单射线假设失效）。** 定理 4.2 用到共现事件恒为 $u+v$ 这一条射线。若共现事件为 $\alpha u+\beta v$ 且 $\alpha/\beta$ 可变，一个和原子不能同时精确重构所有共现点，引理 4.1 的等号在这些点上不可达，最优几何可能是部分吸收或更多原子；文献的玩具实验在幅值可变时报告部分吸收（第 7 章表）。本卷对该情形不作断言。

**开放问题 5.6（两原子全局最优的解析刻画）。** 对 $p_B>0$，在所有单位范数二原子字典上刻画 $\arg\min\mathcal J$，判定极小点是否唯一、$d_1$ 是否离开 $u$、极小点是否随 $p_B/p_{AB}$ 连续单调。缺的一步是两原子同时活跃区域内 KKT 分片的显式合并。

**开放问题 5.7（富特征区的纤维陈述）。** 在特征学习区是否存在以时变 $K(\theta(t))$ 表述的延迟泛化定理，使评注 3.2 所记的对数平移律以某种修正形式成立。本卷未证，也未见文献给出。

**可证伪预测 5.8（预登记）。** 对固定特征的线性模型或只训练最后一层的网络，在权重衰减 $\lambda>0$、$P^\perp\theta(0)\ne0$ 下，预测三件可白盒测量的事：（a）$\|P^\perp\theta(t)\|$ 对数线性、斜率 $-\lambda$；（b）投影逃逸读数 $\varphi(x)^\top P^\perp\theta(t)=e^{-\lambda t}b(x)$（把当前参数投到 $\ker\Phi$ 后读出）恒等于 $e^{-\lambda t}b(x)$，把初始化沿 $\ker\Phi$ 的分量放大 $s$ 倍时，凡原进入时刻 $T_\varepsilon(x)>0$ 者恰增加 $\lambda^{-1}\log s$ 而训练曲线逐点不变（定理 3.1（i）与评注 3.2）；（c）当 $\langle a,b\rangle\ge0$、$b\ne0$ 时归约超出量的对数斜率落在 $[-2\lambda,-\lambda]$（评注 3.2）。**不**预测全预测误差 $|a(x)+s(t)b(x)+\varphi(x)^\top E(t)|$ 的进入时刻精确平移，也不预测“测试预测减去岭预测”的进入时刻精确平移（后者仍含瞬态 $\varphi(x)^\top E(t)$）：$\Phi=(1,0)$、$y=0$、$\lambda=1$、$\theta(0)=(1,1)$、$\varphi(x)=(1,1)$、$y(x)=0$、容差 $\tfrac12$ 时 $a(x)=0$，误差为 $e^{-2t}+e^{-t}$，零空间分量放大四倍后为 $e^{-2t}+4e^{-t}$，进入时刻分别为 $\log(1+\sqrt3)\approx1.0051$ 与 $\log(4+3\sqrt2)\approx2.1093$，平移 $1.1043$ 而非 $\log4\approx1.3863$。命题 6.1 在一个六维实例上给出（a）（b）（c）的精确值；在真实的非线性网络上它们是猜想，若实测的平移与 $\lambda^{-1}\log s$ 系统偏离，被反驳的是“线性化图景可外推到该网络”这一猜想，不是本章的定理。

## 6. 一个六维实例

**命题 6.1（有理实例，repo-derived）。** 取 $N=3,p=6$，
$$
\Phi=\begin{pmatrix}1&0&1&0&0&0\\0&1&0&1&0&0\\0&0&1&1&1&0\end{pmatrix},\qquad
\theta^\star=\Phi^\top(1,-1,2)^\top=(1,-1,3,1,2,0)^\top,\qquad y=\Phi\theta^\star=(4,0,6)^\top,
$$
测试特征 $(0,1,0,0,0,1),(0,0,0,0,1,1),(1,0,0,1,0,0),(0,1,1,0,0,0)$ 及目标 $y_{\rm test}=\varphi^\top\theta^\star=(-1,2,2,2)$，初始化 $\theta(0)=(3,-2,5,4,-1,6)^\top$，$\lambda=1/20$。则 $\Phi\Phi^\top$ 的特征值为 $1,2,4$（$\sigma_N^2=1$），
$$
P^\perp\theta(0)=\big(-\tfrac14,-\tfrac94,\tfrac14,\tfrac94,-\tfrac52,6\big)^\top,\qquad
b=\big(\tfrac{15}4,\tfrac72,2,-2\big),\qquad
a=\Big(\tfrac{3341}{69741},-\tfrac{82}{1701},-\tfrac{2}{1701},-\tfrac{2}{1701}\Big),
$$
$\langle a,b\rangle=\tfrac{3047}{278964}>0$，$\|b\|^2=\tfrac{549}{16}$，平台值 $L_\infty=\tfrac{11580382}{1621269027}\approx7.1428\times10^{-3}$。逃逸读数的进入时刻 $T_\varepsilon(x)=\max\{0,20\log(|b(x)|/\varepsilon)\}$，把 $P^\perp\theta(0)$ 放大四倍后每个 $T_\varepsilon(x)>0$ 恰增加 $20\log4\approx27.726$；归约超出量的对数斜率落在 $[-0.1,-0.05]$。

证明。$\Phi\Phi^\top=\begin{pmatrix}2&0&1\\0&2&1\\1&1&3\end{pmatrix}$ 的特征多项式为 $(t-1)(t-2)(t-4)$。$P^\perp\theta(0)$、$\theta_\lambda=\Phi^\top(\Phi\Phi^\top+\tfrac1{20}I)^{-1}y$、$a$、$b$ 与 $L_\infty$ 都是有理算术，逐项按约定 1.2 与评注 3.2 所记的岭残差计算即得；后两句是评注 3.2 所记的进入时刻与对数斜率在 $\langle a,b\rangle>0$、$b\ne0$ 下的直接代入。证毕。

## 7. 来源与文献状态

| 来源 | 精确范围与使用边界 |
| --- | --- |
| Engl, Hanke, Neubauer, *Regularization of Inverse Problems*, Kluwer 1996, 第 5 章（库内条目 [englhankeneubauer1996regularization](../../../Library/Dynamics/englhankeneubauer1996regularization.md)） | `literature-attested`：定理 2.3 的 Tikhonov 极限；不用于任何动态陈述 |
| Hoerl, Kennard, *Ridge Regression: Biased Estimation for Nonorthogonal Problems*, Technometrics 12 (1970)；Hastie, Tibshirani, Friedman, *The Elements of Statistical Learning*, 2nd ed., §3.4.1（库内条目 [hoerlkennard1970ridge](../../../Library/Dynamics/hoerlkennard1970ridge.md)、[hastietibshiranifriedman2009elements](../../../Library/Dynamics/hastietibshiranifriedman2009elements.md)） | `literature-attested`：岭解与岭残差（定理 3.1 证明中的不动点、评注 3.2 的平台值）是经典代数，本卷只在中间步骤验证 |
| Searle, *Linear Models*, Wiley 1971（可估函数与行空间）（库内条目 [searle1971linear](../../../Library/Dynamics/searle1971linear.md)） | `literature-attested`：定理 3.1 的机制——零空间分量不可估——是经典可估性理论；本卷的贡献只是把它写成训练曲线读数的逃逸集并给出进入时刻的见证 |
| Jacot, Gabriel, Hongler, *Neural Tangent Kernel*, NeurIPS 2018, arXiv:1806.07572（库内条目 [jacot2018neural](../../../Library/Dynamics/jacot2018neural.md)） | `literature-attested`：评注 3.4 所用线性化的定义及其无限宽、有限时间的成立条件；不用于有限宽网络的定理，也不支持任何失效时刻的断言 |
| Li, Wang, Arora, *What Happens after SGD Reaches Zero Loss? A Mathematical Framework*, ICLR 2022, arXiv:2110.06914（库内条目 [liwangarora2022zero](../../../Library/Dynamics/liwangarora2022zero.md)） | `literature-attested`：零损失流形上的极限流形流形式（标签噪声 SGD）；定理 2.4 只用逐点陈述 |
| Levi, Beck, Bar-Sinai, *Grokking in Linear Estimators – A Solvable Model that Groks without Understanding*, ICLR 2024, arXiv:2310.16441（库内条目 [levibeckbarsinai2023grokking](../../../Library/Dynamics/levibeckbarsinai2023grokking.md)） | `literature-attested`：线性师生模型在权重衰减下可解的延迟泛化；其式 (12) 另给无权重衰减时由近零谱模态造成的延迟，正是评注 3.3 所说“慢的行模态”的高维实例。定理 3.1 证明中的精确解是其动力学的特化，本卷的增量只是定理 3.1 的逃逸集表述 |
| Boursier, Pesme, Dragomir, *A Theoretical Framework for Grokking: Interpolation followed by Riemannian Norm Minimisation*, NeurIPS 2025, arXiv:2505.20172（库内条目 [boursierpesmedragomir2025grokking](../../../Library/Dynamics/boursierpesmedragomir2025grokking.md)）；Musat, *The Geometry of Grokking: Norm Minimization on the Zero-Loss Manifold*, arXiv:2511.01938（库内条目 [musat2025geometry](../../../Library/Dynamics/musat2025geometry.md)） | `literature-attested`：小权重衰减下插值流形上的慢时间 Riemann 范数极小流（命题 2；Morse–Bott 条件）与其几何先例；其附录 C 式 (24) 已给线性回归零坐标 $e^{-\lambda t}$ 衰减。定理 2.4 只用逐点陈述，定理 3.1 证明中的零空间项与之相同 |
| Xu, Vardi, Safran, *To Grok Grokking: Provable Grokking in Ridge Regression*, ICML 2026, arXiv:2601.19791（库内条目 [xuvardisafran2026grok](../../../Library/Dynamics/xuvardisafran2026grok.md)） | `literature-attested`：岭回归梯度下降的可证延迟泛化，定理 A.2 给零空间分量递推 $(1-\eta\lambda)^t$，式 (8) 给人口阈值时刻关于初始化方差对数的下界；评注 3.2 所记的对数平移律是其连续时间精确形式 |
| Kim, *Grokking on the Weight-Decay Clock: A Rate Hierarchy from Softly Broken Symmetries*, arXiv:2607.23967（库内条目 [kim2026weightdecayclock](../../../Library/Dynamics/kim2026weightdecayclock.md)） | `literature-attested`：经验可观测 Gram 与人口可观测 Gram 的零空间之商作为内在对象（§2.3），慢模态时钟（定理 4、推论 5），人口风险超出量的单根/双根速率二分（定理 20）及重标经验零分量的对数平移实验（§7.4）；定理 3.1 的“训练不可见”框架与评注 3.2 所记的速率二分均以此为先例，本卷只提供逃逸集表述与显式见证 |
| Gu, Chen, Zhang, Hu, Cao, *Beyond Progress Measures: Theoretical Insights into the Mechanism of Grokking*, arXiv:2504.03162（库内条目 [guchenzhanghucao2025beyond](../../../Library/Dynamics/guchenzhanghucao2025beyond.md)） | `literature-attested`：以目标相等的输入商刻画算法任务上的 grokking；只用于说明该商在输入侧，不是参数方向的训练不可见商 |
| Xu, Wang, Frei, Vardi, Hu, *Benign Overfitting and Grokking in ReLU Networks for XOR Cluster Data*, arXiv:2310.02541（库内条目 [xuwangfreivardihu2023benign](../../../Library/Dynamics/xuwangfreivardihu2023benign.md)）；Mohamadi, Li, Wu, Sutherland, *Why Do You Grok? A Theoretical Analysis of Grokking Modular Addition*, ICML 2024, arXiv:2407.12332（库内条目 [mohamadiliwusutherland2024grok](../../../Library/Dynamics/mohamadiliwusutherland2024grok.md)） | `literature-attested`：无权重衰减、小初始化、特征学习下的可证延迟泛化，与模加法上核区到富区的样本复杂度分离；只用于反例 5.2 的边界 |
| Lyu, Jin, Li, Du, Lee, Hu, *Dichotomy of Early and Late Phase Implicit Biases Can Provably Induce Grokking*, ICLR 2024, arXiv:2311.18817（库内条目 [lyujinlidulee2023dichotomy](../../../Library/Dynamics/lyujinlidulee2023dichotomy.md)） | `literature-attested`：大初始化加小权重衰减先核区后富区的两阶段图景；本卷不重证其定理，也不据此断言线性化失效时刻（评注 3.4） |
| Kumar, Bordelon, Gershman, Pehlevan, *Grokking as the Transition from Lazy to Rich Training Dynamics*, ICLR 2024, arXiv:2310.06110（库内条目 [kumarbordelongershmanpehlevan2023grokking](../../../Library/Dynamics/kumarbordelongershmanpehlevan2023grokking.md)） | `literature-attested`：懒区到富区转变解释延迟泛化的论证；用于反例 5.2 的边界 |
| Liu, Michaud, Tegmark, *Omnigrok: Grokking Beyond Algorithmic Data*, ICLR 2023, arXiv:2210.01117（库内条目 [liumichaudtegmark2022omnigrok](../../../Library/Dynamics/liumichaudtegmark2022omnigrok.md)） | `literature-attested`：初始化范数与权重衰减控制延迟泛化的经验结论；与评注 3.2 所记的对数时钟方向一致 |
| Nanda, Chan, Lieberum, Smith, Steinhardt, *Progress Measures for Grokking via Mechanistic Interpretability*, ICLR 2023, arXiv:2301.05217（库内条目 [nandachanlieberumsmithsteinhardt2023progress](../../../Library/Dynamics/nandachanlieberumsmithsteinhardt2023progress.md)） | `literature-attested`：白盒进度量的概念与模加法电路；评注 3.2 只借用“进度量”一词 |
| Power, Burda, Edwards, Babuschkin, Misra, *Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets*, arXiv:2201.02177（库内条目 [powerburdaedwardsbabuschkinmisra2022grokking](../../../Library/Dynamics/powerburdaedwardsbabuschkinmisra2022grokking.md)） | `literature-attested`：现象的原始报告 |
| Prieto, Barsbey, Mediano, Birdal, *Grokking at the Edge of Numerical Stability*, ICLR 2025, arXiv:2501.04697；Thilak, Littwin, Zhai, Saremi, Paiss, Susskind, *The Slingshot Mechanism*, arXiv:2206.04817（库内条目 [prietobarsbeymedianobirdal2025grokking](../../../Library/Dynamics/prietobarsbeymedianobirdal2025grokking.md)、[thilaklittwinzhaisaremipaisssusskind2022slingshot](../../../Library/Dynamics/thilaklittwinzhaisaremipaisssusskind2022slingshot.md)） | `literature-attested`：无权重衰减的延迟泛化报告；只用于反例 5.2 的边界 |
| Parikh, Boyd, *Proximal Algorithms*, Foundations and Trends in Optimization 1(3) (2014)，§6.5.1；Chandrasekaran, Recht, Parrilo, Willsky, *The Convex Geometry of Linear Inverse Problems*, Found. Comput. Math. 12 (2012)（库内条目 [parikhboyd2014proximal](../../../Library/SparseCoding/parikhboyd2014proximal.md)、[chandrasekaranrechtparrilowillsky2012convex](../../../Library/SparseCoding/chandrasekaranrechtparrilowillsky2012convex.md)） | `literature-attested`：欧氏范数的近端收缩 $\lambda\|x\|-\lambda^2/2$ 与原子范数框架；引理 4.1 的下界是其直接后果，本卷加的是三角不等式取等给出的字典级刻画 |
| Olshausen, Field, *Emergence of simple-cell receptive field properties by learning a sparse code for natural images*, Nature 381 (1996)（库内条目 [olshausenfield1996emergence](../../../Library/SparseCoding/olshausenfield1996emergence.md)） | `literature-attested`：稀疏编码目标的来源 |
| Geng, Wang, Wright, *On the Local Correctness of $\ell^1$-Minimization for Dictionary Learning*, arXiv:1101.5672（ISIT 2014 版为 Geng, Wright）；Gribonval, Schnass, *Dictionary Identification—Sparse Matrix-Factorisation via $\ell_1$-Minimisation*, arXiv:0904.4774（库内条目 [gengwangwright2011local](../../../Library/SparseCoding/gengwangwright2011local.md)、[gribonvalschnass2010dictionary](../../../Library/SparseCoding/gribonvalschnass2010dictionary.md)） | `literature-attested`：在“满足 $AX=Y$ 且列归一的因子化流形”上极小化系数 $\ell_1$，即重构纤维内由稀疏性裁决的经典形式；评注 4.8 的纤维读法不是新框架。两者的局部可辨识定理假设随机支撑，不适用于本卷的层级支撑 |
| Elhage 等, *Toy Models of Superposition*, Transformer Circuits Thread 2022；Bricken 等, *Towards Monosemanticity*, 2023（库内条目 [elhage2022toy](../../../Library/SparseCoding/elhage2022toy.md)、[bricken2023monosemanticity](../../../Library/SparseCoding/bricken2023monosemanticity.md)） | `literature-attested`：叠加与稀疏自编码器的背景；第 4 章不使用其任何定理 |
| Chanin, Wilken-Smith, Dulka, Bhatnagar, Golechha, Bloom, *A is for Absorption: Studying Feature Splitting and Absorption in Sparse Autoencoders*, NeurIPS 2025, arXiv:2409.14507（v6，2025-11-17）（库内条目 [chanin2024absorption](../../../Library/SparseCoding/chanin2024absorption.md)） | `literature-attested`：特征吸收的经验报告，含“加大字典或改稀疏度不消除吸收”（摘要原话）；v6 附录 A.2 命题 1–2 给出严格层级、正交二值特征下解码列 $f_2+\delta f_1$（非单位范数）保持精确重构而使期望 $\ell_1$ 从 $2p_{11}+p_{10}$ 降到 $(2-\delta)p_{11}+p_{10}$ 的下降族，是吸收的稀疏激励的先例，不是全局极小刻画 |
| Chanin, *Toy Models of Feature Absorption in SAEs*, LessWrong 2024-10-07（库内条目 [chanin2024toymodels](../../../Library/SparseCoding/chanin2024toymodels.md)） | `literature-attested`：共现率与幅值可变下的吸收与部分吸收的玩具实验报告；用于反例 5.5 的边界 |
| Till, *Do sparse autoencoders find “true features”?*, LessWrong 2024-02-22；Anders, Neo, Hoelscher-Obermaier, Howard, *Sparse autoencoders find composed features in small toy models*, LessWrong 2024-03-14（库内条目 [till2024truefeatures](../../../Library/SparseCoding/till2024truefeatures.md)、[andersneohoelscherobermaierhoward2024composed](../../../Library/SparseCoding/andersneohoelscherobermaierhoward2024composed.md)） | `literature-attested`：“高频共现可被复合特征替代”的定性论证与解码归一化下的复合特征实验；引理 4.1 给出其精确形式 |
| MAIS-A3 研究草稿, *The geometry and identifiability of superposition*（https://github.com/lionellevine/MAIS，路径 `agendas/A3/MAIS-A3.tex`，提交 84b81190dfe64c8627f19589e4b5a0700fa68bf7，作者栏“Claude Fable 5, audited by GPT 5.6 Sol”，2026-07）（库内条目 [mais2026superposition](../../../Library/SparseCoding/mais2026superposition.md)） | `literature-attested`（低状态来源，非同行评审）：命题“Positive-penalty merging”——两个嵌套事件、单位系数、无噪声、特征夹角 $\theta\in(0,\pi/2]$，对每个 $\lambda\in(0,1)$，二原子字典上的唯一全局极小是合并对；证明用 $\|\Psi z\|\le\|z\|_1$ 与径向界 $\lambda r-\lambda^2/2$，与引理 4.1 的论证同形，定理 4.2 的二原子正交情形即其陈述。本卷自证的增量是任意原子数、逐点等号刻画、命题 4.3 与命题 4.7 |
| Dorrell, *How Optimality Structures Sparse Dictionaries: A Theory for Understanding SAE Representations*, arXiv:2606.02385（库内条目 [dorrell2026optimality](../../../Library/SparseCoding/dorrell2026optimality.md)） | `literature-attested`：含解码偏置与非负码的一般局部最优必要条件，严格层级除完全对齐外违反该条件；与第 4 章方向一致，本卷不使用其定理 |
| Nelson, Karaletsos, Locatello, *Toward Identifiable Sparse Autoencoders*, arXiv:2605.31245（库内条目 [nelsonkaraletsoslocatello2026identifiable](../../../Library/SparseCoding/nelsonkaraletsoslocatello2026identifiable.md)） | `literature-attested`：SAE 近似可辨识条件（支撑丰富性、支撑内系数多样性）；严格层级违反其丰富性假设，故该定理不适用于本卷玩具模型 |
| Bussmann, Nabeshima, Karvonen, Nanda, *Learning Multi-Level Features with Matryoshka Sparse Autoencoders*, arXiv:2503.17547；Leask 等, *Sparse Autoencoders Do Not Find Canonical Units of Analysis*, arXiv:2502.04878（库内条目 [bussmannnabeshimakarvonennanda2025matryoshka](../../../Library/SparseCoding/bussmannnabeshimakarvonennanda2025matryoshka.md)、[leask2025canonical](../../../Library/SparseCoding/leask2025canonical.md)） | `literature-attested`：层级特征与非规范单元的经验背景 |
| Gao 等, *Scaling and Evaluating Sparse Autoencoders*, arXiv:2406.04093；Rajamanoharan 等, *Jumping Ahead: JumpReLU SAEs*, arXiv:2407.14435；Bussmann, Leask, Nanda, *BatchTopK Sparse Autoencoders*, arXiv:2412.06410；Plascencia, *A Dominant Diffuse Phase in the Sparse Autoencoder Phase Diagram*, arXiv:2609.10299（库内条目 [gao2024scaling](../../../Library/SparseCoding/gao2024scaling.md)、[rajamanoharan2024jumprelu](../../../Library/SparseCoding/rajamanoharan2024jumprelu.md)、[bussmannleasknanda2024batchtopk](../../../Library/SparseCoding/bussmannleasknanda2024batchtopk.md)、[plascencia2026diffuse](../../../Library/SparseCoding/plascencia2026diffuse.md)） | `literature-attested`：TopK、JumpReLU、批级 TopK 目标的定义（命题 4.6 只用理想单原子编码器的定义）；层级—惩罚—宽度扫描中弥散相占主导的经验相图，提示实际训练的 SAE 未必落在本卷比较的两类字典上 |
| — | `repo-derived`（本卷自证的陈述）：命题 2.2；定理 2.4；定理 3.1；定理 4.2 的任意原子数与等号刻画；命题 4.3；定理 4.4；命题 4.5；命题 4.6；命题 4.7；反例 5.1、5.4；命题 6.1 |
| — | `suspected-novel`（新颖性未经证实）：定理 4.4 的显式两点阈值 $\rho^\ast(\lambda)$；命题 4.5 的端点导数陈述（文献只有经验报告与一般必要条件）；命题 4.6 的 $p_B<2p_{AB}$；命题 4.7。第 3 章不列任何新项：零空间分量的 $e^{-\lambda t}$ 衰减、对数时钟与速率二分分别见于 Boursier 等、Xu–Vardi–Safran、Kim 与 Omnigrok 的启发式，已按第 3.8 条只作评注记账；定理 3.1 只是经典不可估性加 RRO 判据的改写并附显式见证；引理 4.1 与定理 4.2 的二原子情形在 MAIS-A3 草稿中已有同形证明，也不列为新。检索范围：2020–2026 年 arXiv/OpenReview/LessWrong 与 Transformer Circuits 线程，关键词 null space / kernel-orthogonal initialization / weight decay grokking time、feature absorption theory、dictionary learning unit-norm ℓ1 composite atoms，另含 Chanin v6 附录 A.2 与 MAIS-A3 的命题原文。未命中只说明在此范围内未找到，不推出原创 |

**推导关系。** 逐条注明各陈述相对于所引结果与前文的推导关系：定理 2.4、命题 4.6 与命题 6.1 是对前文定理或定义的直接特化与规范化；评注 3.2–3.4 只记账已知结果，不承担新内容；引理 4.1 的下界是所引经典结果的重证；定理 4.2 的极小点刻画、命题 4.3 与命题 4.7 都只是引理 4.1 的逐点应用与按正概率加权求和（4.3 另加正交坐标下的逐坐标收缩）；定理 3.1（i）（ii）是其证明中所引精确解的直接推论，（iii）是约定 1.1 加 RRO 判据的应用，（iv）给出实际见证。含有本卷自己计算的是命题 2.2 的三阶展开、定理 3.1（iv）的见证、定理 4.4 的费用表与两段 $\Delta_v$、命题 4.5 的两端导数。

## 追加锚（本行以下为增补区）
