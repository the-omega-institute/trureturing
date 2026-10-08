# FIB 的双曲几何与相位边界

**约定 0.1（共同来源与任务）。** 本卷的离散来源是自由有序 FIB 树及其五模式窗口代表；连续对象是明确定义的组成表示，参数默认属于 $\mathbb R$。复相位、实线性状态、概率律、已取得档案分别是不同类型的对象。原生窗口按高到低读取，印刷位次仍为低、中、高；非法动作保留独立的吸收拒绝结果。连续表示不增加原生动作菜单，不供应未知律、复制、重置或组合物理仪器。

**数学引文 0.2（已有数学与本卷的关系）。** 固定仓内来源为快照 [4e2c5f4beebcc598aa440c500397da133e6f5da0](https://github.com/the-omega-institute/trureturing/tree/4e2c5f4beebcc598aa440c500397da133e6f5da0)。[关系延拓几何 §§1、3、7](FIB_RELATIONAL_CONTINUATION_GEOMETRY.md) 供应树组成、未来闭合判据及总化原生读者；[二阶关系完成 §§1、39、53、66、110、112](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md) 已有两次数量恢复、五函数和概率反解、局部量子接口及共同环境返回的边界。[稳定关系边界 §§7.3–7.5](AURIC_FIB_STABLE_RELATION_BOUNDARY_THREE_DIMENSIONAL_CLOSURE.md) 已有五代表和零贡献区别；[观察者内生三轴 §§8–10](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md) 已有一般联合线性来源的未来不变核与同源桥。[金字塔关联与原生接续 §§3–4、8](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md) 已有占位均值纤维；[金字塔行列式与原生守卫接续 §10.4–10.6](AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md) 已有实际继续窗口 $[5]$ 的回复表。这些结果在此直接消费。

标量黄金恒等式、Binet 与 Fibonacci 矩阵是 [Koshy 的既有文献输入](../../../Library/notes/koshy2001fibonacci.md)。复幂和双曲函数取 [DLMF 的定义](../../../Library/Analytic/dlmfcomplexpowerhyperbolic.md)。[Özvatan–Pashaev v1 §5.1](../../../Library/notes/ozvatanpashaev2017binetcurves.md) 已有采用 $+\pi$ 的连续 Binet 曲线。[Higham 的 2006 章稿](../../../Library/Quantum/higham2006eigenstate.md)，原文 §3 的定义与 Facts 1–2、§4 Fact 3，供应矩阵指数、自治流与负特征值实对数的经典背景；这里指 *Handbook of Linear Algebra* 的章稿，不指后来的同名专著。第一至六节的经典计算作为第七节共同来源桥的中间步骤展开，不另计为新的基础定理。本卷的仓内推导是第七节：同一五贡献的连续提升与投影未来闭合、整条均值曲线的完整概率纤维，以及既有原生继续回复对这些纤维的严格细化。

## 一、固定分支：整数奇偶与连续相位

**定义 1.1（下侧分支与双曲读出）。** 置

```math
\varphi=\frac{1+\sqrt5}{2},\qquad a=\log\varphi>0,\qquad
\psi=-\varphi^{-1},\qquad i^t=e^{i\pi t/2}.
```

选取 $\log(i\varphi)=a+i\pi/2$，并选取 $\psi$ 的下侧对数值 $L_-=-a-i\pi$；所有非整数幂均按这份选择定义。令

```math
\mathcal F(t)=\frac{2}{\sqrt5\,e^{i\pi t/2}}
\sinh\bigl((a+i\pi/2)t\bigr).
```

负实轴两侧的对数值相差 $2\pi i$；本定义不是把不同底数的主值对数任意相加。由 [DLMF 4.2.28、4.28.1](../../../Library/Analytic/dlmfcomplexpowerhyperbolic.md) 的定义，直接有

```math
\begin{aligned}
\mathcal F(t)
&=\frac{e^{-i\pi t/2}}{\sqrt5}
\left(e^{(a+i\pi/2)t}-e^{-(a+i\pi/2)t}\right)\\
&=\frac{e^{at}-e^{(-a-i\pi)t}}{\sqrt5}.
\end{aligned}
```

对实 $t$，实虚部因而为

```math
\Re\mathcal F(t)=\frac{\varphi^t-\varphi^{-t}\cos(\pi t)}{\sqrt5},
\qquad
\Im\mathcal F(t)=\frac{\varphi^{-t}\sin(\pi t)}{\sqrt5}.
```

实部是指数增长项减去指数衰减的振荡修正，不是有界周期波。对 $n\in\mathbb Z$，$e^{-i\pi n}=(-1)^n$，故经典 Binet 式给

```math
\mathcal F(n)=\frac{\varphi^n-\psi^n}{\sqrt5}=F_n.
```

这里 $F_0=0,F_1=1$，整数递推向正负两端延伸。将 $L_-$ 换为 $L_+=-a+i\pi$ 得 $B_+(t)$，对实参数恰有 $B_+(t)=\overline{\mathcal F(t)}$；整数点仍相同。这正是所引连续 Fibonacci 论文 §5.1 的相反分支。若扩展到复参数 $z$，正确关系是 $B_+(z)=\overline{\mathcal F(\bar z)}$，不能省去参数上的共轭。

## 二、负指标：反向必须携带复相位

**推导 2.1（固定分支的反向关系）。** 在定义 1.1 下，对每个实 $t$，

```math
\mathcal F(-t)=-e^{i\pi t}\mathcal F(t).
```

证明是完整的指数代入：

```math
\begin{aligned}
-e^{i\pi t}\mathcal F(t)
&=-\frac{e^{at+i\pi t}-e^{-at}}{\sqrt5}\\
&=\frac{e^{-at}-e^{at+i\pi t}}{\sqrt5}
=\mathcal F(-t).
\end{aligned}
```

于是整数时恢复 [Koshy 的负指标 Binet 关系](../../../Library/notes/koshy2001fibonacci.md)：

```math
F_{-n}=(-1)^{n+1}F_n,\qquad
F_{-1}=1,\quad F_{-2}=-1,\quad F_{-3}=2,\quad F_{-4}=-3,\quad F_{-5}=5.
```

非整数时不能把 $(-1)^{t+1}$ 当成只有正负两值的实符号。例如本分支给

```math
\mathcal F(1/2)=\frac{\sqrt\varphi+i/\sqrt\varphi}{\sqrt5},\qquad
\mathcal F(-1/2)=\frac{1/\sqrt\varphi-i\sqrt\varphi}{\sqrt5}
=-i\mathcal F(1/2).
```

若记 $R(t)=\Re\mathcal F(t)$、$I(t)=\Im\mathcal F(t)$，则实部的准确反向式是

```math
R(-t)=-\cos(\pi t)R(t)+\sin(\pi t)I(t).
```

证明只须展开 $-e^{i\pi t}(R+iI)$。半整数例中 $R(-1/2)$ 与 $R(1/2)$ 的绝对值不同，已排除“只对实部交替乘正负一”的扩展。

## 三、FIB 一步：正交反射与保面积双曲伸缩

**定义 3.1（组成层、欧氏尺子与反射）。** 原生自由树为

```math
T::=\alpha\mid\beta\mid\langle T,T\rangle,
\qquad \rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
```

组成是叶数列向量，$c(\alpha)=(1,0)^{\mathsf T}$、$c(\beta)=(0,1)^{\mathsf T}$，对子加法。供应的组成桥为

```math
c(\rho T)=Mc(T),\qquad M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
```

来源的左右次序、括号和记录仍在树层；$M$ 只推进组成。在扩展的 $\mathbb R^2$ 上采用标准欧氏内积及标准定向，令

```math
S=\frac{2M-I}{\sqrt5}
=\frac1{\sqrt5}\begin{pmatrix}-1&2\\2&1\end{pmatrix}.
```

**推导 3.2（第七节使用的经典谱分解）。** 直接乘出 $M^2=M+I$、$\det M=-1$，特征值为 $\varphi,\psi$。因此

```math
S^{\mathsf T}=S,\qquad S^2=I,\qquad \det S=-1.
```

$S^{\mathsf T}S=I$，所以它是上述欧氏尺子下的正交反射，正负特征方向各一维。[Higham §3 的指数级数](../../../Library/Quantum/higham2006eigenstate.md) 按偶奇项分组给

```math
e^{sS}=\cosh s\,I+\sinh s\,S.
```

黄金关系 $\varphi-\varphi^{-1}=1$、$\varphi+\varphi^{-1}=\sqrt5$ 给

```math
\sinh a=\frac12,\qquad \cosh a=\frac{\sqrt5}{2},\qquad
Se^{aS}=\frac{\sqrt5}{2}S+\frac12I=M.
```

这完整证明 $M=Se^{aS}$。伸缩 $e^{aS}$ 的正特征值为 $e^a,e^{-a}$，所以其行列式为一、在实组成平面保有向面积；反射使 $M$ 每步反定向。两因子可交换，均可逆，因而对所有 $n\in\mathbb Z$ 有

```math
M^n=S^n e^{naS}.
```

负整数幂在扩展实组成层有意义，不因此成为原生树上的逆替换。

**推导 3.3（圆与双曲线的不同平方关系）。** 同一指数级数对

```math
K=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad K^2=-I
```

给 $e^{\theta K}=\cos\theta\,I+\sin\theta\,K$；对 $S^2=I$ 则给上述双曲式。前者在欧氏平面旋转，后者在谱坐标中作互逆伸缩。于是

```math
2\sinh a=1,\qquad 2\cosh a=\sqrt5,\qquad
(\sqrt5)^2=1^2+2^2.
```

这是双曲恒等式 $\cosh^2a-\sinh^2a=1$ 的标量标定，可用 $1,2,\sqrt5$ 直角三角形表示；它不为来源额外供应尺子。经典 Binet 式分奇偶为

```math
F_{2k}=\frac2{\sqrt5}\sinh(2ka),\qquad
F_{2k+1}=\frac2{\sqrt5}\cosh((2k+1)a),\qquad k\in\mathbb Z.
```

证明：偶指数时 $\psi^{2k}=e^{-2ka}$，奇指数时 $\psi^{2k+1}=-e^{-(2k+1)a}$，代入第一节即可。复双曲读出借选定相位把这两个整数分支装入同一表达式。

## 四、二维实群的障碍与复群的 Cassini 相位

**定义 4.1（同一状态空间的一参数群要求）。** 要求 $T(t)$ 是实二维线性算子，定义于全部实 $t$，并满足 $T(0)=I$、$T(s+t)=T(s)T(t)$、$T(1)=M$。该要求不只是画一条标量曲线。

**推导 4.2（平方行列式障碍与两步边界）。** 即使不要求连续性，定义 4.1 也不可能成立：群律给 $M=T(1/2)^2$，但

```math
-1=\det M=\bigl(\det T(1/2)\bigr)^2\ge0
```

矛盾。这是实平方根的经典行列式障碍；[Higham §4 Fact 3](../../../Library/Quantum/higham2006eigenstate.md) 的一般实对数条件也排除这个单负特征线。它不排除穿过整数值的实标量曲线。只连续化两步则可取 $V(t)=e^{2atS}$，因 $M^2=e^{2aS}$；这里 $V(1)=M^2$，并未细分原来的一步。允许复状态或增加实方向是不同的表示合同。

**定义 4.3（下侧谱分支的复线性群）。** 在 $\mathbb C^2$ 上令

```math
P_\pm=\frac{I\pm S}{2},\qquad
U(t)=e^{at}P_++e^{(-a-i\pi)t}P_-.
```

由 $P_\pm^2=P_\pm$、$P_+P_-=0$、$P_++P_-=I$，完整得到

```math
U(0)=I,\qquad U(s+t)=U(s)U(t),\qquad U(1)=M,\qquad U(n)=M^n.
```

最后一个等式对所有正负整数成立，因为群律也给逆。指数群是 [Higham §3](../../../Library/Quantum/higham2006eigenstate.md) 的自治矩阵指数应用，其生成元是 $aP_++(-a-i\pi)P_-$。

**推导 4.4（移位矩阵及复 Cassini）。** 代入 $S$ 的显式矩阵，并置 $b=e^{(-a-i\pi)t}$，得

```math
U(t)=\frac12\begin{pmatrix}
e^{at}+b-(e^{at}-b)/\sqrt5&2(e^{at}-b)/\sqrt5\\
2(e^{at}-b)/\sqrt5&e^{at}+b+(e^{at}-b)/\sqrt5
\end{pmatrix}.
```

第一节的指数式给 $\mathcal F(t)=(e^{at}-b)/\sqrt5$，并给

```math
\mathcal F(t-1)=\frac{\varphi^{-1}e^{at}+\varphi b}{\sqrt5},\qquad
\mathcal F(t+1)=\frac{\varphi e^{at}+\varphi^{-1}b}{\sqrt5}.
```

利用 $\varphi=(1+\sqrt5)/2$，对角项正好是这两个值，故

```math
U(t)=\begin{pmatrix}
\mathcal F(t-1)&\mathcal F(t)\\
\mathcal F(t)&\mathcal F(t+1)
\end{pmatrix}.
```

在两个谱线上的特征值乘积为 $e^{at}e^{(-a-i\pi)t}$，因此

```math
\det U(t)=e^{-i\pi t},\qquad
\mathcal F(t+1)\mathcal F(t-1)-\mathcal F(t)^2=e^{-i\pi t}.
```

整数点恢复经典 Cassini 的正确符号 $F_{n+1}F_{n-1}-F_n^2=(-1)^n$。整数时它描述实组成平面平行四边形的有向面积反号；非整数复行列式属于复线性表示，不是普通实空间面积。它的相位也不是在此建立的量子相干度。

## 五、整个二维输入的三维实自治嵌入与投影返回

**定义 5.1（固定嵌入与同一实线性流）。** 取正交单位谱基

```math
v_+=\frac{(1,\varphi)^{\mathsf T}}{\sqrt{1+\varphi^2}},\qquad
v_-=\frac{(1,\psi)^{\mathsf T}}{\sqrt{1+\psi^2}}.
```

它们内积为零，因为 $\varphi\psi=-1$；分别是 $M$ 的 $\varphi,\psi$ 特征向量。对整个 $\mathbb R^2$，固定实线性映射

```math
Jc=(\langle v_+,c\rangle,\langle v_-,c\rangle,0).
```

$J$ 单射，其像是固定的 $Z=0$ 平面。对 $\mathbb R^3$ 的全部初态定义同一流

```math
\begin{aligned}
X(t)&=e^{at}X_0,\\
Y(t)&=e^{-at}\bigl(Y_0\cos(\pi t)-Z_0\sin(\pi t)\bigr),\\
Z(t)&=e^{-at}\bigl(Y_0\sin(\pi t)+Z_0\cos(\pi t)\bigr).
\end{aligned}
```

记此算子为 $T_3(t)$，生成元为

```math
G=\begin{pmatrix}a&0&0\\0&-a&-\pi\\0&\pi&-a\end{pmatrix},\qquad
T_3(t)=e^{tG}.
```

指数伸缩与平面旋转的和角公式直接给自治群律。若初态是 $Jc$，则每个 $n\in\mathbb Z$ 都有

```math
T_3(n)Jc=\bigl(\varphi^n\langle v_+,c\rangle,
\psi^n\langle v_-,c\rangle,0\bigr)=JM^nc.
```

这验证的是整个二维输入的交织，包含负整数；不只是一条特殊轨道。

**推导 5.2（该自治线性嵌入类的最小维数）。** 要求固定实线性单射 $J_d:\mathbb R^2\to\mathbb R^d$，同一个实线性连续一参数群 $T_d$，且 $T_d(n)J_d=J_dM^n$ 对全部整数成立。单射先给 $d\ge2$。若 $d=2$，$J_d$ 可逆，$T_d(1)=J_dMJ_d^{-1}$ 行列式为负，而 $T_d(1/2)^2=T_d(1)$，违反第四节的障碍。定义 5.1 给 $d=3$ 的构造，故此类的最小维数恰为三。所用矩阵指数和旋转块是所引 Higham 的经典工具。

这是状态表示的维数，参数 $t$ 仍一维。带外部已知时钟 $t$ 和初始组成 $c_0$ 的公式 $U(t)c_0$ 是另一种充分预测表示：它调用时钟依赖的读出，不满足这里同一自治线性状态嵌入的全部要求。非线性编码、受限来源格点及物理空间维数也不属于这个最小性命题。

**定义 5.3（复读出与实投影）。** 对全部三维态定义

```math
L(X,Y,Z)=Xv_++(Y-iZ)v_-,\qquad
B(X,Y,Z)=Xv_++Yv_-.
```

因为旋转后 $Y-iZ=e^{(-a-i\pi)t}(Y_0-iZ_0)$，有

```math
LT_3(t)=U(t)L,\qquad LJ=I,\qquad
LT_3(t)J=U(t),\qquad BT_3(t)J=\Re U(t).
```

正向实旋转与负频复谱一致，靠的是 $Y-iZ$ 这份约定。特殊初值 $(X_0,Y_0,Z_0)=(1,1,0)$ 还满足

```math
\mathcal F(t)=\frac{X(t)-Y(t)+iZ(t)}{\sqrt5}.
```

这里最后的标量读口不同于 $L$ 的向量读口和原生数量行 $q=(2,3)$；它们共享所声明的流，不因此成为同一实际仪器。

**推导 5.4（实投影不闭合的精确缺陷）。** 对实组成令

```math
A(t)=\Re U(t)=e^{at}P_++e^{-at}\cos(\pi t)P_-.
```

展开投影乘积并用余弦和角式，得

```math
A(s+t)-A(s)A(t)
=-e^{-a(s+t)}\sin(\pi s)\sin(\pi t)P_-.
```

因此一般不能只保存当前实部，再以 $A(s)$ 当成合法的自治继续算子。若 $h\in1/2+\mathbb Z$，则 $A(h)=e^{ah}P_+$，在完整实输入域的核为 $\mathbb R v_-$。取同一时钟 $h=1/2$ 和输入 $c_0=0,c_1=v_-$，它们的当前实投影都为零；继续模型时间 $s=1/2$ 后，实投影差却为 $\psi v_-\ne0$。两个真实提升态在当前分别为 $0$ 和 $(0,0,e^{-a/2})$，所以关系只是转到未读坐标，没有被完整流删除。

在全部 $\mathbb R^3$ 上，当前 $B$ 的核为 $\mathbb R(0,0,1)$；$BT_3(1/2)(0,0,1)=-e^{-a/2}v_-\ne0$。于是

```math
\bigcap_{s\ge0}\ker(BT_3(s))=\{0\}.
```

证明：$s=0$ 先迫使隐藏差只在第三坐标，$s=1/2$ 再迫使该坐标为零。这是本流的具体未来闭合，使用已有一般未来核判据；$B$ 单独却不是充分状态。

**推导 5.5（格点域不能由秩下降推出碰撞）。** 半时刻在实域不单射，但在精确 $\mathbb Q^2$，因而在 $\mathbb Z^2$ 组成上，$A(h)$ 仍单射。证明：若两个有理输入之差在 $\mathbb Rv_-$，其坐标比必须是无理数 $\psi$；有理差若首坐标非零则不可能，首坐标为零又迫使整差为零。原生确定树组成是非负整数，所以前述全实态例子不能冒充两棵整数树的半时刻碰撞。第七节会给同一个五模式域上合法的实概率均值碰撞，并在原生菜单内指出后续见证；这仍不授予原生半步。

## 六、整数值与递推不能唯一决定连续插值

**定义 6.1（奇数频率分支族）。** 对每个 $k\in\mathbb Z$ 定义

```math
\mathcal F_k(t)=\frac{e^{at}-e^{(-a+i(2k+1)\pi)t}}{\sqrt5}.
```

本卷是 $k=-1$ 的分支；所引 [Özvatan–Pashaev §5.1](../../../Library/notes/ozvatanpashaev2017binetcurves.md) 是 $k=0$。整数时 $e^{i(2k+1)\pi n}=(-1)^n$，所以所有分支都给 $F_n$。两个指数的一步因子分别为 $\varphi,\psi$，各满足 $r^2=r+1$，故对每个实 $t$ 有

```math
\mathcal F_k(t+2)=\mathcal F_k(t+1)+\mathcal F_k(t).
```

不同 $k$ 的负频项比为 $e^{2\pi i(k-\ell)t}$，不是恒一；其导数在零处相差 $-2\pi i(k-\ell)/\sqrt5$，所以非整数曲线不同。它们均是整函数；连续性、解析性及这份实参数递推合在一起也没有选出唯一分支。

**推导 6.2（固定分支之外还有周期调制）。** 即使先指定 $\mathcal F$，对任意常数 $\lambda\in\mathbb C$，函数

```math
\widetilde{\mathcal F}(t)=\mathcal F(t)+\lambda e^{at}\sin(2\pi t)
```

仍保留所有整数值与同一递推。证明：附加项 $g$ 在整数点为零，且 $g(t+1)=\varphi g(t)$、$g(t+2)=\varphi^2g(t)=(\varphi+1)g(t)$。当 $\lambda\ne0$ 时，例如 $t=1/4$ 的值改变。该函数仍整解析。它不必是固定生成元的同一双指数谱轨道；若另加生成元或增长条件来筛选插值，应由那些条件单独证明唯一性，整数递推本身没有提供它们。

树上的 $\rho$ 是离散替换。上述连续群只延拓组成表示；$\rho^{1/2}$、任意实参数逆树替换都未由树语法定义。组成层的可逆矩阵、曲线连续性与谱相位不能代替这项来源操作义务。

## 七、同一五模式律：连续提升、整条均值纤维与原生未来

**定义 7.1（五贡献、概率律与实际读者）。** 使用同一集合 $\Sigma=\{0,2,5,25,3\}$，并依次记概率为 $p=(p_0,p_2,p_5,p_{25},p_3)$，各项非负且和为一。五模式的占位、所选来源代表及组成贡献是

| 标签 | $(x,y,z)$ | 所选来源代表 | $d_\sigma$ | $q d_\sigma$ |
| --- | --- | --- | --- | ---: |
| $[null]$ | $(0,0,0)$ | 空选择贡献 | $(0,0)^{\mathsf T}$ | $0$ |
| $[2]$ | $(1,0,0)$ | $\alpha$ | $(1,0)^{\mathsf T}$ | $2$ |
| $[5]$ | $(0,1,0)$ | $\langle\beta,\alpha\rangle$ | $(1,1)^{\mathsf T}$ | $5$ |
| $[25]$ | $(1,1,0)$ | $\langle\langle\beta,\alpha\rangle,\alpha\rangle$ | $(2,1)^{\mathsf T}$ | $7$ |
| $[3]$ | $(0,0,1)$ | $\beta$ | $(0,1)^{\mathsf T}$ | $3$ |

$[25]$ 是同窗两端选择，既非第六位置，也非数量十或二十五。空选择的组成贡献是零，不是自由树，也不表示实际 $[null]$ 动作为恒等。

原生状态为 $(s,C)$，$s\in\{0,1\}$、$C\in\mathbb N^2$，初态 $(0,0)$。窗口 $\sigma$ 仅在 $s\,y(\sigma)=0$ 时合法；合法时

```math
C'=HC+d_\sigma,\qquad s'=x(\sigma),\qquad
H=M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\qquad q=(2,3).
```

读出为 $qC'$，非法时进入并留在独立错误态 $\bot$。这里用 $H$ 命名窗口运输，避免与第三节反射 $S$ 混用。实际 $[null]$ 把旧组成变成 $HC$ 并把接缝置零，故在非零旧态上仍有运输与回复。固定律 $p$ 声明的是从初态合法读一次窗口的来源分布，不是已经取得的档案，也不声明多次抽样独立。

**定义 7.2（同源连续数量响应）。** 在同一 $\sigma$ 上定义提升与读出

```math
z_\sigma(t)=T_3(t)Jd_\sigma,\qquad
f_\sigma(t)=qLz_\sigma(t)=qU(t)d_\sigma.
```

整数 $n\ge0$ 时它是所选贡献经 $n$ 次组成替换后的数量；非整数时是声明的表示读出，不是新增实际动作。由第四节矩阵及递推，逐项有

```math
\begin{aligned}
f_2(t)&=2\mathcal F(t-1)+3\mathcal F(t)=\mathcal F(t+3),\\
f_3(t)&=2\mathcal F(t)+3\mathcal F(t+1)=\mathcal F(t+4),\\
f_0(t)&=0,\qquad f_5(t)=f_2(t)+f_3(t),\\
f_{25}(t)&=2f_2(t)+f_3(t).
\end{aligned}
```

第一式由三次递推得到 $\mathcal F(t+3)=3\mathcal F(t)+2\mathcal F(t-1)$；第二式同理。这给 $t=0$ 时的 $0,2,5,7,3$，也固定了整族来源对应。

**定理 7.3（同一律的提升交换与两种信息损失）。** 对定义 7.1 的同一概率律，令

```math
X=p_2+p_{25},\qquad Y=p_5+p_{25},\qquad Z=p_3,\qquad
u=X+Y,\qquad v=Y+Z,\qquad \bar c=(u,v)^{\mathsf T}.
```

则整个均值提升、复数量曲线及实组成投影恰为

```math
\begin{aligned}
\bar z_p(t)&=\sum_\sigma p_\sigma z_\sigma(t)=T_3(t)J\bar c,\\
\bar f_p(t)&=qL\bar z_p(t)=u\mathcal F(t+3)+v\mathcal F(t+4),\\
\bar r_p(t)&=B\bar z_p(t)=A(t)\bar c.
\end{aligned}
```

整条 $\bar f_p$ 相等，当且仅当 $\bar c$ 相等。相比之下，半时刻 $h\in1/2+\mathbb Z$ 的 $\bar r_p(h)$ 相等，当且仅当 $P_+(\bar c_p-\bar c_{p'})=0$；在完整实均值域，后一个关系严格更粗。

证明。表中直接给 $\sum p_\sigma d_\sigma=(p_2+p_5+2p_{25},p_3+p_5+p_{25})^{\mathsf T}$。固定律的有限求和可与每个线性映射交换，故前三式完全作用于同一来源。整条曲线至少包含 $t=0,1$，它们给

```math
\binom{\bar f_p(0)}{\bar f_p(1)}
=\begin{pmatrix}2&3\\3&5\end{pmatrix}\binom uv,\qquad
u=5\bar f_p(0)-3\bar f_p(1),\quad
v=-3\bar f_p(0)+2\bar f_p(1).
```

行列式为一，故曲线相等迫使 $u,v$ 相同；反向由曲线公式。两次数量恢复是第二阶卷 §1 的既有输入，这里将它接在同一个 $p$ 的五贡献与连续提升上。半时刻条件由 $A(h)=e^{ah}P_+$ 直接给出。

为证明严格性确实发生在这份来源域而非任意拼接实态，取按本卷顺序的合法律

```math
p^{\circ}=(1/5,1/5,1/5,1/5,1/5),\qquad
p^\epsilon=p^{\circ}+\epsilon\bigl(-(1+\psi),1,0,0,\psi\bigr),\qquad
\epsilon=1/20.
```

因为 $-1<\psi<0$，所有概率仍严格正，增量和为零，且

```math
\bar c_{p^\epsilon}-\bar c_{p^{\circ}}=\epsilon(1,\psi)^{\mathsf T}.
```

这恰是负谱方向。二律在 $h=1/2$ 的实投影相同，完整提升的第三坐标却不同；继续表示时间 $1/2$ 后 $A(1)$ 把差送到 $\epsilon\psi(1,\psi)^{\mathsf T}\ne0$。整条数量曲线也不同，因为 $q(1,\psi)^{\mathsf T}=2+3\psi\ne0$。这些律有实的无理概率，不能转述为精确有理概率计数或确定整数树的碰撞。∎

**定理 7.4（同源半投影损失的原生未来见证）。** 对定理 7.3 的二律，首次窗口合法输入以后，在同一历史上继续原生窗口 $[null]$。它对两律所有支撑模式均合法，下一数量均值之差恰为

```math
\epsilon qM^3(1,\psi)^{\mathsf T}
=\epsilon\psi^3(2+3\psi)\ne0.
```

因此半时刻实投影不能作为这份来源上原生未来数量均值任务的充分摘要；它的丢失不是永久的全曲线核。

证明。首次输入从 $(0,0)$ 得 $C=d_\sigma,s=x(\sigma)$。$[null]$ 的最高位为零，故无论接缝为零或一都合法；下一状态为 $(0,M^3d_\sigma)$，回复 $qM^3d_\sigma$。在同一个来源律上取期望，再用负特征向量的三次推进，便得所列差。$\psi\ne0$，且 $2+3\psi=0$ 会迫使 $\psi=-2/3$，与 $\psi^2=\psi+1$ 不符，所以差非零。

表示时间的继续 $1/2$ 与实际窗口继续 $[null]$ 是两个声明域的不同动作，证明只通过共同 $d_\sigma,p$ 接上它们，不将二者识别成同一个物理操作。已知时钟加初始均值可另行预测这些量，却不是只保存当前投影。该反例消费第五节的返回方向和原生零窗口运输，保持真实接缝、拒绝类型与来源合同。∎

**定理 7.5（整条均值曲线的精确全部纤维）。** 定义 7.1 的全部概率律在 $p\mapsto\bar f_p$ 下的像可用

```math
\mathcal D=\{(u,v):0\le v\le1,\quad 0\le u\le1+v\}
```

参数化。对给定 $(u,v)\in\mathcal D$，整条同曲线纤维恰为以下全部律，没有遗漏边界：

```math
\begin{aligned}
\max\left(0,\frac{u+v-1}{2}\right)&\le y\le\min(u,v),\\
\max(0,u+v-y-1)&\le\kappa\le\min(u-y,y),\\
(p_0,p_2,p_5,p_{25},p_3)
&=(1-u-v+y+\kappa, u-y-\kappa, y-\kappa, \kappa, v-y).
\end{aligned}
```

这里 $y=Y$、$\kappa=p_{25}$。在归一化概率超平面内，相同曲线之差的线性核恰由

```math
g_y=(1,-1,1,0,-1),\qquad g_\kappa=(1,-1,-1,1,0)
```

张成；严格正内点的纤维局部为二维，某些边界纤维可降维或为单点。

证明。定理 7.3 已把同曲线条件精确化为同 $u,v$。固定 $y$ 后 $X=u-y,Z=v-y$；既有金字塔概率反解 $p_2=X-\kappa,p_5=Y-\kappa,p_3=Z,p_0=1-X-Y-Z+\kappa$ 正好给所列参数式。逐概率非负，等价于 $y\le v$ 及

```math
\kappa\ge0,\quad \kappa\ge u+v-y-1,\quad
\kappa\le u-y,\quad \kappa\le y.
```

存在这样的 $\kappa$，等价于 $y\ge0$、$y\le u$、$v\le1$、$2y\ge u+v-1$。这给第一行区间及第二行区间，反向代入则每项非负且和为一。

存在 $y$ 又等价于 $0\le v\le1,0\le u\le1+v$：必要性由 $v=p_3+p_5+p_{25}\le1$、$u\ge0$，以及 $u-v=p_2+p_{25}-p_3\le1$；充分性时第一行下端不大于 $u$ 和 $v$，再选区间内任意 $y,\kappa$。故像和所有边界均已覆盖。参数式对 $y,\kappa$ 的差给上述两个独立向量。反过来，归一化与两个组成均值的三条线性约束秩为三，因为 $p_0,p_2,p_3$ 的三列独立，核维数二，所以没有第三个自由差。

这些参数对 $\bar c$、$\bar z_p(t)$、$\bar f_p(t)$ 在所有时刻都不可见。这是同一来源律到均值的永久核；半时刻 $P_-$ 的暂时投影损失则作用于已经形成的 $\bar c$，两者属于连续的不同映射，不能互相替代。∎

**命题 7.6（不同金字塔位置而同整条均值曲线）。** 合法来源

```math
\mu_A=\tfrac12\delta_0+\tfrac12\delta_5,\qquad
\mu_B=\tfrac12\delta_2+\tfrac12\delta_3
```

分别给 $(X,Y,Z)=(0,1/2,0)$ 与 $(1/2,0,1/2)$，却都给 $(u,v)=(1/2,1/2)$，故对每个实 $t$ 有 $\bar f_{\mu_A}(t)=\bar f_{\mu_B}(t)$。

证明。直接代入概率及定理 7.3，或用 $f_5=f_2+f_3$。这两个点对应定理 7.5 中 $y=1/2$ 与 $y=0$，两者均可取 $\kappa=0$。但首次数量分布分别为 $\tfrac12\delta_0+\tfrac12\delta_5$ 与 $\tfrac12\delta_2+\tfrac12\delta_3$，已经不同；均值曲线相等没有给出完整数量律相等，更未给出已取得档案相等。增加这同一均值读口的采样密度不会切开该纤维。∎

**定义 7.7（已有原生继续回复的同源任务）。** 在定义 7.1 的首次实际窗口以后，沿该历史继续固定窗口 $[5]$。保留回复 $R\in\{5,18,26,\bot\}$，其中拒绝与任意合法数量可区分。该任务正是所引第十卷的原生继续表；这里使用其未经条件化的完整回复律 $\nu_p$，不新增仪器，也不假定可以免费复制首次来源。

**定理 7.8（原生继续回复严格细化全曲线纤维）。** 在上述同一来源合同内，逐模式回复与概率为

| 首次模式 | 首次后接缝 | 原生继续 $[5]$ 的回复 |
| --- | ---: | --- |
| $[null]$ | $0$ | $5$ |
| $[2]$ | $1$ | $\bot$ |
| $[5]$ | $0$ | $26$ |
| $[25]$ | $1$ | $\bot$ |
| $[3]$ | $0$ | $18$ |

```math
\nu_p(5)=p_0,\qquad \nu_p(18)=p_3,\qquad
\nu_p(26)=p_5,\qquad \nu_p(\bot)=p_2+p_{25}.
```

在每条定理 7.5 的同曲线纤维内，$p\mapsto\nu_p$ 单射。因而精确的整条均值曲线加精确的该继续回复律足以恢复完整五模式律；这是一项同源充分性结论，不是最少新增统计量或未知律已取得的结论。

证明。首次输入从空接缝出发均合法，之后接缝为 $x$。继续 $[5]$ 的最高位为一，故 $[2],[25]$ 分支拒绝且保留 $\bot$；另外三支的数量为

```math
q(Hd_0+d_5)=5,\qquad
q(Hd_3+d_5)=13+5=18,\qquad
q(Hd_5+d_5)=21+5=26.
```

由同一 $p$ 推前得到所列律。若再保留第十卷的奇偶档案事件 $A=\{3,5,25\}$，其概率为 $v$，$v>0$ 时条件回复概率依次为 $p_3/v,p_5/v,p_{25}/v$，对应 $18,26,\bot$；这与已有条件公式完全一致。

现在只用未经条件化的 $\nu_p$。由曲线取回 $u,v$，设 $b=\nu_p(\bot)$、$c=\nu_p(26)$。则在同源合法像上

```math
y=u-b,\qquad \kappa=u-b-c,\qquad
p_{25}=\kappa,\quad p_2=b-\kappa,\quad
p_5=c,\quad p_3=\nu_p(18),\quad p_0=\nu_p(5).
```

证明：$b=X=u-y$，$c=p_5=y-\kappa$。所有分量遂被逐项恢复，且 $v=c+\kappa+\nu_p(18)$ 自动满足同源相容式。这在非退化纤维及全部退化边界都成立，无须条件事件概率非零。等价地，同曲线差 $\delta y g_y+\delta\kappa g_\kappa$ 在四个回复概率中的差为

```math
(\delta y+\delta\kappa, -\delta y,
\delta y-\delta\kappa, -\delta y)
```

，按回复 $5,18,26,\bot$ 排列。若全为零，先由第二项得 $\delta y=0$，再得 $\delta\kappa=0$，所以此回复确实切开全曲线的全部残余纤维。

命题 7.6 的二律给 $\nu_{\mu_A}=\tfrac12\delta_5+\tfrac12\delta_{26}$ 与 $\nu_{\mu_B}=\tfrac12\delta_\bot+\tfrac12\delta_{18}$；相同整条均值曲线而原生未来回复不同。因此曲线摘要不是这份原生回复任务的充分边界。拒绝不能删除后重新归一化成“双方都可继续”的比较，否则已经改变任务。

同一律上的精确回复分布是本命题的前提；实际一次回复只是一个样本，未知 $p$ 不由该样本或一份有限档案自动恢复。数量 $0,2,5,7,3$ 虽对模式单射，已取得的精确数量可确定该次模式，仍不等于取得完整来源概率律。各反事实输入的数学回复表也不等于它们已经在同一个未知初态上全部执行。∎

**命题 7.9（共同来源桥的结论与范围）。** 在定义 7.1–7.2 的合同内，下列关系同时成立：整条连续均值曲线与初始组成均值等价；半时刻实投影可暂时合并不同的实律均值，且已有原生零窗口运输能见证后续差；完整实提升保留该返回方向；相同组成均值的概率纤维却在全部连续均值时刻永久合并，而已有原生继续回复可切开它。三维最小性只适用于第五节的固定全二维实线性自治嵌入。

证明。第一项由定理 7.3 的两次反解，第二项由定理 7.3–7.4 的严格正同源二律，第三项由 $LT_3(t)J=U(t)$ 及第五节的未来核，第四项由定理 7.5 与 7.8。第五节的单射和平方障碍给最后的精确范围。所有步骤共享五贡献、初接缝、概率律与指定读出，没有把单独的经典分解或相同维数当成来源桥。

因此 $\varphi,\varphi^{-1}$ 对应互逆伸缩，$(-1)^n$ 对应整数反射奇偶，$e^{-i\pi t}$ 对应所选谱路径的中间相位，$\sinh,\cosh$ 对应互逆指数的差与和，$\Re U(t)$ 对应该路径的一个投影。连续化补足中间路径，却没有自动补足来源可区分性。这里的谱相位没有供应量子相干来源或相位读口，模型状态三维没有推出物理空间三维，复群逆没有定义原生逆树替换，完整均值曲线没有替代完整数量／回复律或已取得档案。∎

## 追加锚（本行以下为增补区）
