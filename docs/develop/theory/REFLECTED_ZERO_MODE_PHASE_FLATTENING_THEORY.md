# 反射零点模式与相位压平理论
## 从临界位移、频率与辅助时间中分离三个反向操作

仓库基线：`the-omega-institute/trureturing` 的 `dev` 分支，分支创建时提交为 `2deefdd8b7de08ef84311b00fed4f60516194fba`。

本卷承接负性、负平方与负时间理论。前一层指出，反射增长率对 `delta` 与 `-delta` 的一阶和为零，有符号行列式为 `-delta^2`。本层进一步把这一通用双曲结构接到仓库已经冻结的 zeta 零点生成元坐标，并严格区分函数方程反射、复共轭和辅助模式时间反演。

本卷不是 RH 证明声明。这里的 `time` 是指数模式参数，不被解释为物理时间。所有关于 completed zeta、Weil 正性和全局谱完成的结论仍需额外桥梁。

## 一、归一化零点生成元

对任意复点

$$
rho=sigma+i gamma,
$$

定义相对临界线的有符号横向位移

$$
delta(rho)=\operatorname{Re}rho-\frac12.
$$

仓库现有 `CriticalDampingGenerator` 在消去统一阻尼平移后留下的标量生成元为

$$
\boxed{
g(rho)=-delta(rho)+i\operatorname{Im}rho.
}
$$

于是定义辅助指数模式

$$
\boxed{
M_rho(t)=\exp(g(rho)t).
}
$$

生成元实部控制幅度变化，虚部控制相位旋转：

$$
\operatorname{Re}g(rho)=-delta(rho),
\qquad
\operatorname{Im}g(rho)=\operatorname{Im}rho.
$$

因此

$$
\overline{g(rho)}=-g(rho)
$$

当且仅当

$$
\operatorname{Re}rho=\frac12.
$$

这与现有零点族级别的 skew-adjoint 判据相容。本层把它提升为任意单点的明确坐标恒等式。

## 二、径向通道与相位通道

定义径向通道

$$
R_rho(t)=\exp(-delta(rho)t),
$$

以及公共相位通道

$$
P_rho(t)=\exp(i\operatorname{Im}(rho)t).
$$

则

$$
\boxed{
M_rho(t)=R_rho(t)P_rho(t).
}
$$

相位通道满足

$$
|P_rho(t)|=1.
$$

所以模式的模长完全由横向位移控制：

$$
|M_rho(t)|=\exp(-delta(rho)t).
$$

定义相位压平观察

$$
\operatorname{Flat}(rho,t)
=M_rho(t)\exp(-i\operatorname{Im}(rho)t).
$$

则精确得到

$$
\boxed{
\operatorname{Flat}(rho,t)=R_rho(t).
}
$$

相位压平没有近似误差，也不需要选择对数分支。它只利用整个函数 `exp` 的乘法恒等式。

## 三、三个容易混淆的反向操作

### 1. 函数方程反射

定义

$$
F(rho)=1-rho.
$$

若 `rho` 的坐标为 `(delta,gamma)`，则

$$
F:(delta,gamma)\mapsto(-delta,-gamma).
$$

生成元满足

$$
g(F(rho))=-g(rho).
$$

因此

$$
\boxed{
M_{F(rho)}(t)=M_rho(-t).
}
$$

函数方程反射在辅助模式层等同于完整生成元的时间反演。它同时翻转径向速率和频率。

### 2. 复共轭

定义

$$
C(rho)=\overline{rho}.
$$

其坐标作用为

$$
C:(delta,gamma)\mapsto(delta,-gamma).
$$

生成元满足

$$
g(C(rho))=\overline{g(rho)}.
$$

模式满足

$$
\boxed{
M_{C(rho)}(t)=\overline{M_rho(t)}.
}
$$

复共轭保留径向增长率，只反转相位绕行方向。它对应负频率，不等同于负时间。

### 3. 同高度临界线镜像

定义

$$
H(rho)=1-\overline{rho}.
$$

其坐标作用为

$$
H:(delta,gamma)\mapsto(-delta,gamma).
$$

它可以写成

$$
H=F\circ C=C\circ F.
$$

生成元满足

$$
g(H(rho))=-\overline{g(rho)}.
$$

相位压平后，`rho` 与 `H(rho)` 的两个径向模式互为倒数：

$$
\boxed{
\operatorname{Flat}(rho,t)\operatorname{Flat}(H(rho),t)=1.
}
$$

这正是离线反射对的增长和衰减双支结构。

## 四、对称方形

三个非平凡变换与恒等变换组成一个 Klein 四群：

$$
\{I,F,C,H\},
\qquad
F^2=C^2=H^2=I,
\qquad
FC=CF=H.
$$

其坐标表为：

| 变换 | 位移 `delta` | 频率 `gamma` | 模式作用 |
| --- | ---: | ---: | --- |
| `I` | `delta` | `gamma` | 原模式 |
| `F` | `-delta` | `-gamma` | 辅助时间反演 |
| `C` | `delta` | `-gamma` | 复共轭 |
| `H` | `-delta` | `gamma` | 同相位的径向互反 |

仓库的 `ZeroData` 已经分别保存 `reflection` 和 `conjugation` 两个零点索引置换。由于零点枚举无重复，两个复平面复合都落到同一个同高度镜像点，从而两个索引置换交换：

$$
\boxed{
R(C(n))=C(R(n)).
}
$$

这里的交换不是额外假设。它由两个零点图像相等和枚举单射性推出。

## 五、临界线的模式含义

当

$$
delta(rho)=0,
$$

径向通道退化为常数一：

$$
R_rho(t)=1.
$$

归一化模式成为纯单位模旋转：

$$
M_rho(t)=\exp(i\gamma t).
$$

因此临界线可以解释为归一化生成元没有径向增长或衰减。离线点则产生一对同相位的互反径向分支。

这个解释与负平方真源相连。若同高度镜像位移为 `delta` 和 `-delta`，对应径向生成率为 `-delta` 和 `delta`，则它们的有符号行列式为

$$
-delta^2.
$$

本层没有重复形式化该行列式，因为相应真源仍在独立 PR 中。本层只冻结从实际零点坐标到径向互反对的精确表示桥。

## 六、形式化边界

同一 PR 的 Lean 真源只建立以下无条件事实：

1. 仓库现有阻尼平移表达式精确化简为 `g(rho)`。
2. `g(rho)` 为 skew 当且仅当 `rho` 位于临界线。
3. `M_rho` 精确分解为径向通道与单位相位通道。
4. 相位压平精确恢复径向通道。
5. 函数方程反射在模式层等于辅助时间反演。
6. 共轭只反转相位频率。
7. 同高度临界线镜像在相位压平后给出互为倒数的径向分支。
8. `ZeroData` 的反射与共轭置换交换。

本层不声明：

- 指数模式参数等于物理时间；
- 所有 `ZeroData` 的构造已经无条件存在；
- completed zeta 是某个有限维动力系统的特征行列式；
- 相位压平本身产生 Weil 或 Pick 负证书；
- 任意离线零点已经被有限测试函数隔离；
- 上述表示桥推出 RH。

## 七、基于形式化真理的下一研究义务

### 1. 二阶谱节点

对径向模式应形式化

$$
\frac{d^2}{dt^2}R_rho(t)=delta(rho)^2R_rho(t),
$$

从而

$$
-\frac{d^2}{dt^2}R_rho(t)=-delta(rho)^2R_rho(t).
$$

这会把有符号行列式 `-delta^2` 升级为实际二阶算子的负谱值，并连接 normal jet。

### 2. 偶奇观察节点

定义

$$
E(t)=\frac{R(t)+R(-t)}2,
\qquad
O(t)=\frac{R(t)-R(-t)}2.
$$

应证明偶通道保存位移平方而丢失方向，奇通道在非零位移下恢复时间定向。

### 3. 负平方 Laplace resolvent

在明确条件 `u>delta^2` 下形式化

$$
\int_0^\infty e^{-(u-delta^2)t}\,dt
=\frac1{u-delta^2}.
$$

这会把负谱值连接到稳定化债务和 resolvent 极点。

### 4. 曲率互作用节点

需要把相位压平后的径向互反对与已有 `OffLineCurvatureDipole` 的法向二阶对数曲率精确连接。目标不是结构类比，而是一个可运输误差和符号的等式。

## 八、更新后的 theorem DAG

```text
CriticalDampingGenerator
        |
        v
ReflectedZeroModePhaseFlattening
        |
        +-----------------------------+
        |                             |
        v                             v
SecondOrderRadialSpectrum       EvenOddModeObserver
        |                             |
        +--------------+--------------+
                       |
                       v
          NegativeSquareLaplaceResolvent
                       |
                       v
          OffLineCurvatureModeIntertwiner
                       |
                       v
             SignedNormalSpectralAtom
                       |
                       v
       Chebyshev / Toeplitz / Pick / Weil witness
```

下一真源的最高优先级是 `ReflectedZeroModeSecondOrderSpectrum`。它将第一次把本层的表示分解变成一个真正的负谱陈述。
