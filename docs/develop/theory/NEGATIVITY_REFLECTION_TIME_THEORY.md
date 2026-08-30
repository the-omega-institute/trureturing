# 负性、负平方与负时间理论
## 反射分裂、观察锥与时间定向研究卷；不是 RH 证明声明

仓库基线：`the-omega-institute/trureturing` 的 `dev` 分支，取阅提交 `23747a66fdb518fd82dbccc6ca5fca0126d6d33c`。

本卷的目标是把“负性”“负平方”“负时间”从直觉词汇拆成可独立审计的数学角色。核心判断是：负号不自带统一含义。它总是相对于一个正锥、允许支撑、时间定向、谱稳定域或二次型而出现。

## 一、负性是相对于正锥的越界

设向量空间或对象空间为 $X$，允许对象形成正锥 $C\subseteq X$。若存在对偶观察器 $\ell$ 满足

$$
\ell(c)\ge 0\qquad(c\in C),
$$

但对某个对象 $x$ 有

$$
\ell(x)<0,
$$

则 $\ell$ 是 $x$ 离开正锥的负性证书。相应定义为

$$
\operatorname{NegativeWitness}_{C}(x)
\;:\Longleftrightarrow\;
\exists\ell\in C^{\vee},\ \ell(x)<0.
$$

因此以下对象应保持强类型区分：

1. 负标量：$a<0$。
2. 负支撑：正质量位于禁止区域，例如 $x<0$。
3. 负质量：测度系数本身为负。
4. 负方向：存在 $v\ne0$ 使二次型 $Q(v)<0$。
5. 负指数：最大负定子空间的维数。
6. 负时间：相对于选定正向时间锥的反向参数或逆向完成。
7. 负频率：Fourier 相位的反向绕行，它不等于过去时间。

这些概念之间可以建立运输定理，不能直接互相替换。

## 二、负平方不是实数平方小于零

对实数 $\delta$，算术平方始终满足

$$
\delta^2\ge0.
$$

本路线所说的“负平方”是

$$
-\delta^2,
$$

即先形成反射不变量 $\delta^2$，再用负号记录该轨道处于允许支撑的另一侧。

在 RH 的法向坐标中，令

$$
\delta=\Re\rho-\frac12.
$$

函数方程反射交换 $\delta$ 与 $-\delta$。反射商空间无法保留左右标签，只能保留偏移大小 $\delta^2$。若还需要记录轨道位于临界线外，则最自然的有符号法向坐标是

$$
\boxed{x_{\perp}=-\delta^2.}
$$

负号表达的是“离线扇区”，不是“平方运算产生了负数”。

## 三、负平方是反射对的最低阶判别式

考虑反射生成率对

$$
+\delta,\qquad-\delta.
$$

一阶和完全抵消：

$$
\delta+(-\delta)=0.
$$

二阶乘积留下：

$$
\delta(-\delta)=-\delta^2.
$$

等价地，对形式谱变量 $r$，有

$$
(r-\delta)(r+\delta)=r^2-\delta^2.
$$

若把生成元写成对角矩阵

$$
A_{\delta}=\begin{pmatrix}\delta&0\\0&-\delta\end{pmatrix},
$$

则

$$
\operatorname{tr}A_{\delta}=0,
\qquad
\det A_{\delta}=-\delta^2,
\qquad
A_{\delta}^2=\delta^2I.
$$

所以 $-\delta^2$ 是反射分裂在一阶抵消后留下的最低阶规范不变量。本卷称它为反射对判别式：

$$
\boxed{\operatorname{ReflectionPairDiscriminant}(\delta)=-\delta^2.}
$$

这解释了为什么反射对称会压平奇数法向层，而二阶 normal jet 仍能识别离线分裂。

## 四、增长与衰减是负平方的时间实现

定义一对指数分支

$$
g_{+}(t)=e^{\delta t},
\qquad
g_{-}(t)=e^{-\delta t}.
$$

它们满足：

$$
g_{+}(-t)=g_{-}(t),
\qquad
g_{-}(-t)=g_{+}(t),
$$

以及

$$
g_{+}(t)g_{-}(t)=1.
$$

因此时间反演不删除分裂，而是交换扩张与收缩分支。

当 $\delta>0$ 且 $t>0$ 时：

$$
g_{+}(t)>1,
\qquad
g_{-}(t)<1.
$$

在负时间方向，两个不等式交换。反射对整体没有选定唯一稳定箭头。稳定性来自观察者选择的时间定向。

对称观察值

$$
g_{+}(t)+g_{-}(t)=2\cosh(\delta t)
$$

是偶函数。其一阶变化在 $t=0$ 消失，二阶变化携带 $\delta^2$。因此只读取对称总量的观察者会看不见一阶分支方向，却仍能在二阶曲率中看见分裂大小。

## 五、负时间的五种角色

必须区分：

1. $t<0$：坐标位于选定原点之前。
2. $t\mapsto-t$：时间反演 involution。
3. $U(-t)=U(t)^{-1}$：可逆动力学的逆向演化。
4. $\omega<0$：负频率或反向相位绕行。
5. 度量中的 $-dt^2$：时间方向在不定二次型中的符号。

只有第三项要求演化构成群。耗散、投影、测量与粗粒化通常只给出 $t\ge0$ 的半群。此时负时间不是已有单值算子的简单延伸，而是一个过去完成问题。

若前向观察为

$$
q:X\to Y,
$$

则给定当前读数 $y$ 的全部可能过去为

$$
\operatorname{PastFiber}(y)=\{x\in X:q(x)=y\}.
$$

当 $q$ 非单射时，逆向时间是集合值 completion fiber。加入足够记忆后，提升映射

$$
\widetilde q:X\to Y\times M
$$

可能恢复单射，从而在完成后的状态空间中恢复双向时间。

## 六、负支撑、负方向与 negative square

对测度

$$
\nu=\sum_jm_j\delta_{x_j},
$$

“负质量”指 $m_j<0$。“负支撑”指 $m_j>0$ 但 $x_j<0$。当前 RH normal-resolvent 路线更自然地把异常放在支撑位置：

$$
m_{\rho}>0,
\qquad
x_{\rho}=-\delta^2<0.
$$

若测试函数 $p$ 在允许支撑 $[0,\infty)$ 上非负，而在 $-\delta^2$ 处为负，则

$$
\int p(x)\,d\nu(x)<0.
$$

这把负支撑运输成负矩，再运输成 Toeplitz、Pick 或 Weil 二次型的负方向。

对于 Hermitian 核 $K$，有限采样矩阵

$$
G_{jk}=K(z_j,z_k)
$$

若存在 $c\ne0$ 使

$$
c^{*}Gc<0,
$$

则出现一个 negative square。负平方指数是最大独立负子空间的维数。它记录系统拥有多少个彼此独立的向下方向。

## 七、负平方与 Laplace 时间的桥

对适当的 $u$，有形式恒等式

$$
\frac1{u+x}=\int_0^{\infty}e^{-ut}e^{-xt}\,dt.
$$

若 $x>0$，则 $e^{-xt}$ 在正时间衰减。若 $x=-\delta^2<0$，则

$$
e^{-xt}=e^{\delta^2t}
$$

在正时间增长。因此：

$$
\boxed{
\text{负支撑}
\Longleftrightarrow
\text{前向增长模式}
\Longleftrightarrow
\text{逆向衰减模式}
}
$$

这是负平方与负时间最直接的解析桥。该桥需要单独形式化其收敛域和积分身份，不能仅凭形式表达进入真值层。

## 八、与离线零点曲率 dipole 的关系

对离线反射对，当前仓库已有曲率真源

$$
K_{\delta,\gamma}(t)
=2\frac{(t-\gamma)^2-\delta^2}
{((t-\gamma)^2+\delta^2)^2}.
$$

分子

$$
(t-\gamma)^2-\delta^2
$$

正是一个不定二次型。区域 $|t-\gamma|<|\delta|$ 为负核心，外部为正翼，总质量为零。故离线缺陷是一种局部重分配，而不是总质量损失。零频率或只读取总积分的观察器无法检测它。

这要求后续证书同时记录：

- 分辨尺度；
- 负核心的可见质量；
- 正翼污染；
- 截断和运输误差；
- 剩余严格裕量。

## 九、本轮形式化边界

与本卷同一 PR 中的 Lean 真源只冻结以下无条件事实：

1. 交换两个指数分支等于时间反演。
2. 两个分支的乘积恒为一。
3. 反射生成率对的迹为零。
4. 反射对判别式精确等于 $-\delta^2$。
5. 特征因子为 $r^2-\delta^2$。
6. 在 $\delta>0,t>0$ 时，一支严格扩张，另一支严格收缩。
7. 对称分支和是时间偶函数。

本轮不声明：

- zeta ordinate 是物理时间；
- completed zeta 已经拥有该指数 realization；
- 任意离线零点已经被有限观察器隔离；
- 全局 signed normal spectral measure 已构造；
- 上述一般结构推出 RH。

## 十、后续 theorem DAG

```text
ReflectedGrowthPairNegativeSquare
        |
        +--> ReflectionPairDiscriminant
        |
        +--> ForwardExpansionBackwardContraction
        |
        +--> EvenObserverFirstOrderBlindness
        |
        v
NegativeSquareLaplaceResolvent
        |
        v
SignedNormalSpectralAtom
        |
        v
ChebyshevNegativeSupportSeparator
        |
        v
FiniteMomentNegativeWitness
        |
        v
Toeplitz/Pick/Weil Negative Direction
```

紧邻的下一真源应是 `NegativeSquareLaplaceResolvent`。它应在明确条件 $u>\delta^2$ 下机器证明

$$
\int_0^{\infty}e^{-(u-\delta^2)t}\,dt
=\frac1{u-\delta^2},
$$

并证明当 $\delta>0$ 时，负平方支撑对应的时间因子 $e^{\delta^2t}$ 严格增长。该节点会把本轮的有限代数判别式接入 resolvent、Stieltjes、normal jet 与 causal passivity 路线。
