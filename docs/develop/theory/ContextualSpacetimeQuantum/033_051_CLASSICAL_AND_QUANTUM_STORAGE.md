# 情境时空算术的量子扩展：经典与量子存储

[总目](../CONTEXTUAL_SPACETIME_ARITHMETIC_QUANTUM.md) · [前卷](017_032_REFERENCE_AND_CONTROL.md) · [续卷](053_071_PREDICTION_AND_READOUT.md)


<a id="entry-105"></a>

## 追加锚（新终端）

<a id="section-33"></a>

## 33. 一个经典判别比特达到全部参数域的记忆最优值

**定理 33.1（达到最优值不需要在记忆中保留相干）。** 沿用定义 22.1 的可操作记忆任务及全部参数 $\beta_t\in[0,1]$，令

$$
f=\beta_N,\qquad a=1-f,
\qquad s=\prod_{t=1}^{N-1}\sqrt{1-\beta_t},
\qquad E=1-s^2.
$$

对任意有限 $N\ge1$，存在一个使用二维记忆 $M$、无惰性参考、共同输入为 $|0\rangle_S|0\rangle_M$ 的允许协议，达到

$$
\frac12\|\rho^{\rm A}_{H_NM}-\rho^{\rm J}_{H_NM}\|_1
=U(E,f)
=\frac{f+\sqrt{(a+1)^2-4as^2}}2.
$$

该协议的记忆在一个固定正交基中始终为经典寄存器：在离散模型的每个控制和仪器节点之后，两候选的联合态均可写为

$$
\sum_{m=0}^1\sigma^{\rm A/J}_{H_tS,m}\otimes|m\rangle\langle m|_M,
\qquad \sigma^{\rm A/J}_{H_tS,m}\ge0.
$$

特别地，$M$ 与其余保留系统之间没有纠缠，且不需要保留不同记忆标签之间的相干。前 $N-1$ 次读取完全不操作 $M$；只有末次读取之前，才把一个二结果判别测量的结果写入 $M$，并把 $S$ 重置为 $|0\rangle$。

这里的经典性指上述离散 CPTP 控制模型中的保留寄存器，不是对任意微观连续实现作额外断言。活动系统的前缀态与控制仍属于量子任务；本结论只确定达到该指定二元区分目标所需的记忆性质。

证明。使用定理 22.2 的共同无记忆前缀构造。对每个长度 $N-1$ 的历史 $h$，记末次控制之前的实际、理想未归一化系统态为 $\rho_h^{\rm A},\rho_h^{\rm J}$。该构造使用共同初态 $|0\rangle_S$ 及依赖已存历史的共同实系统控制，并满足

$$
\sum_h\operatorname{tr}\rho_h^{\rm A}
=\sum_h\operatorname{tr}\rho_h^{\rm J}=1,
$$

$$
\sum_h\|D_h\|_1
=\sqrt{(a+1)^2-4as^2},
\qquad D_h=a\rho_h^{\rm A}-\rho_h^{\rm J}.
$$

$N=1$ 时前缀为空，唯一的两个候选系统态均为 $|0\rangle\langle0|$，上述恒等式仍成立。$a=0$、零概率历史及全部端点也已由同一定理覆盖。记忆初态为 $|0\rangle_M$，此前始终不变。

对每个 $h$，令 $\Pi_{h,+}$ 为 Hermitian 矩阵 $D_h$ 的严格正谱投影，并令

$$
\Pi_{h,-}=I_S-\Pi_{h,+}.
$$

零谱统一归入负标签；若某一投影为零，相应测量结果就没有概率。这是一个共同的二结果测量，满足

$$
\operatorname{tr}(\Pi_{h,+}D_h)\ge0,
\qquad
\operatorname{tr}(\Pi_{h,-}D_h)\le0,
$$

$$
\sum_{m\in\{+,-\}}
\left|\operatorname{tr}(\Pi_{h,m}D_h)\right|
=\|D_h\|_1.
$$

两投影可以由已知仪器参数、共同输入、共同前缀控制表和旧历史 $h$ 预先计算；计算它们需要使用两个候选模型，但不需要知道实验实际采用了哪个候选。实际与理想过程调用同一个投影对，不发生按真候选选择控制或后选择。

在既有记忆 $M$ 中固定标签 $|+\rangle_M=|0\rangle_M$、$|-\rangle_M=|1\rangle_M$；这里的正负号只是两个正交经典标签，不表示叠加态。把原来的末次 SWAP 替换为共同 $SM$ CPTP 控制

$$
\mathcal F_h(\omega_{SM})
=\sum_{m\in\{+,-\}}
\operatorname{tr}\!\left[(\Pi_{h,m}\otimes I_M)\omega_{SM}\right]
\bigl(|0\rangle\langle0|_S\otimes|m\rangle\langle m|_M\bigr).
$$

这是先测量、再制备的通道：测量效应非负且总和为 $I_{SM}$，输出是归一化的正交标签态与固定系统态，因此完全正且保持迹。它对整个 $SM$ 输入空间都有定义；现有记忆的旧内容被覆盖。测量结果只写入模型已经允许的 $M$，没有向旧历史追加额外永久标签，也没有保留另一个可访问余系统。

定义未归一化的经典记忆概率

$$
p_{h,m}=\operatorname{tr}(\Pi_{h,m}\rho_h^{\rm A}),
\qquad
q_{h,m}=\operatorname{tr}(\Pi_{h,m}\rho_h^{\rm J}).
$$

末次控制之后，两候选系统都为 $|0\rangle$。因此末次实际结果零、一的联合概率分别为 $ap_{h,m},fp_{h,m}$；末次理想结果零、一的联合概率分别为 $q_{h,m},0$。最终差态在经典坐标 $(h,z_N,m)$ 上对角，其对角元素为

$$
d_{h,0,m}=ap_{h,m}-q_{h,m}
=\operatorname{tr}(\Pi_{h,m}D_h),
\qquad
d_{h,1,m}=fp_{h,m}\ge0.
$$

故最终半迹距离为

$$
\begin{aligned}
\frac12\sum_{h,z,m}|d_{h,z,m}|
&=\frac12\left(\sum_h\|D_h\|_1
+f\sum_{h,m}p_{h,m}\right)\\
&=\frac{\sqrt{(a+1)^2-4as^2}+f}{2}
=U(E,f).
\end{aligned}
$$

前缀中 $M$ 始终为固定 $|0\rangle$，而末次控制的输出在固定 $M$ 基上对角，并且 $S$ 是共同固定纯态。末次仪器只作用于 $S$，于是整个离散协议都满足所述记忆经典性与可分性。两候选最终态也是完全经典的联合分布。

该协议属于定理 22.1 的允许类，所以定理 22.2 的上界仍适用；现在给出的经典记忆构造已经达到它。这证明无需在 $M$ 中保留相干，也能达到全部参数域的记忆最优值。证毕。

**推论 33.2（最小经典记忆大小与最终输出压缩）。** 对上述任务，在共同 $SM$ CPTP 控制允许写入经典记忆的条件下，达到 $U(E,f)$ 所需经典记忆的最少标签数与推论 32.2 的 $d_{\min}$ 相同。$N\ge2$ 时为

$$
d_{\min}^{\rm classical}(\boldsymbol\beta)=
\begin{cases}
1,&\beta_N=0\ \text{或}\ \beta_{N-1}=0\ \text{或某个 }\beta_t=1,\\
2,&\beta_N>0,\ \beta_{N-1}>0\ \text{且全部 }\beta_t<1.
\end{cases}
$$

$N=1$ 时为一。即使允许额外任意有限维惰性参考，这个最少标签数也不改变。

此外，对定理 33.1 的达到协议，末端可以先丢弃全部旧历史 $H_{N-1}$，只保留 $(z_N,m)$，而保持半迹距离 $U(E,f)$。再按固定规则把这四个标签压缩成一个最终判别比特 $B$：

$$
B=\begin{cases}
\mathrm A,&z_N=1\ \text{或}\ (z_N=0,m=+),\\
\mathrm J,&z_N=0,m=-,
\end{cases}
$$

得到的两个二元分布仍有总变差距离 $U(E,f)$。这个最后的输出后处理不改变原任务的构造；它说明已输出信息可以进一步压缩，不向协议新增永久输出寄存器。

证明。一个标签对应 $\dim M=1$，属于推论 32.2 已完整分类的无可操作记忆任务；额外惰性参考也包含在该推论的排除范围内。等号边界使用既有无记忆构造即可，其余参数域必须至少有两个标签。定理 33.1 给出两个经典标签的达到，所以这个下界精确。

对于输出压缩，正负谱标签在所有历史上统一。由前面的差坐标公式，固定 $(z,m)$ 后，各历史的差具有同一符号：

$$
d_{h,0,+}\ge0,
\qquad d_{h,0,-}\le0,
\qquad d_{h,1,+},d_{h,1,-}\ge0.
$$

所以逐 $(z,m)$ 合并历史时没有异号抵消，精确有

$$
\sum_{z,m}\left|\sum_h d_{h,z,m}\right|
=\sum_{h,z,m}|d_{h,z,m}|.
$$

丢弃旧历史因此保持最终迹范数。再将三个非负差坐标合并为标签 $\mathrm A$、唯一非正差坐标作为标签 $\mathrm J$，仍没有异号抵消，同样保持迹范数与总变差距离。零差坐标归入任一标签均不影响结论。

这里压缩的是协议结束后的输出。前缀反馈仍允许读取并使用原模型的完整经典历史 $H_t$；本结论没有把控制器在运行期间的总存储压缩成一个比特。这个经典比特只保留为指定候选模型和权重选择的判别结果，不保留可供任意后续量子操作使用的完整状态。因而，推论 32.2 的最小维数二应理解为需要一个额外可写、可读的二标签寄存器，不能单凭该维数结论推断必须使用相干量子存储。

本构造使用标准二元判别的正负谱测量，以及测量后制备的 CPTP 通道。关于正负谱测量的一般最优性，见 Watrous，*The Theory of Quantum Information*，[第 3 章定理 3.4 及式 (3.16)–(3.18)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)；关于测量后制备与纠缠破坏通道的刻画，见 Horodecki、Shor、Ruskai，[*General Entanglement Breaking Channels*（2003），定理 4](https://arxiv.org/abs/quant-ph/0302031)。Bisio、D’Ariano、Perinotti、Sedlak，[*Memory cost of quantum protocols*（2012），§IV](https://arxiv.org/abs/1112.3853) 把量子辅助维数与经典记忆辅助明确区分，并把经典记忆建模为固定正交基上保持对角的寄存器。其资源任务是实现给定量子策略；这里优化的是指定二元区分值，不要求保留该策略对所有后续用途的完整量子输出。证毕。

<a id="entry-107"></a>

## 追加锚（新终端）

<a id="section-34"></a>

## 34. 后揭判别权重与经典存储的两问障碍

**定义 34.1（固定存储之后才揭示权重的二态任务）。** 给定系统 $S=\mathbb C^2$ 上两个已知候选密度算子 $A,J$。实际输入是哪一个候选未知。存储阶段对两个候选使用同一个 CPTP 映射 $\Phi$；权重的两个可能值 $c_1,c_2>0$ 在存储前已知，但最终采用哪一个只在存储结束后揭示，并允许根据揭示的 $c$ 选择最终判别。存储映射不能依赖后来揭示的 $c$。

定义存储前、后的加权判别量

$$
L(c)=\|cA-J\|_1,
\qquad L_\Phi(c)=\|c\Phi(A)-\Phi(J)\|_1.
$$

它们对应先验为 $c/(1+c)$ 与 $1/(1+c)$ 的二态判别；存储后的最优成功概率为

$$
\frac12\left(1+\frac{L_\Phi(c)}{1+c}\right).
$$

有限经典存储指输出在同一固定正交基上对角。它等价于一个有限 POVM $\{E_k\}_{k=1}^m$，满足 $E_k\ge0$、$\sum_kE_k=I$，并具有形式

$$
\Phi(\rho)=\sum_{k=1}^m\operatorname{tr}(E_k\rho)|k\rangle\langle k|.
$$

于是

$$
L_\Phi(c)=\sum_{k=1}^m
\left|\operatorname{tr}\bigl[E_k(cA-J)\bigr]\right|.
$$

这个任务允许最终判别使用全部经典记录和已经揭示的权重；限制只在于存储阶段使用同一个映射。它把权重的揭示时刻作为新假设，不改写前述仪器模型中参数预先给定的约定。

**定理 34.2（两个不同权重排除经典无损存储）。** 在定义 34.1 中，设

$$
A=|u\rangle\langle u|,\qquad
J=|v\rangle\langle v|,
\qquad \|u\|=\|v\|=1,
\qquad 0<|\langle u,v\rangle|<1.
$$

对任意两个不同的正权重 $c_1,c_2$，不存在有限经典存储 $\Phi$ 同时满足

$$
L_\Phi(c_1)=L(c_1),
\qquad L_\Phi(c_2)=L(c_2).
$$

一个量子比特的恒等存储则对全部 $c>0$ 同时保持等号。若最终采用的权重在存储前已经告知存储方，对该权重的一个二元谱测量就能保持等号。

证明。记 $D_c=cA-J$。在 $\operatorname{span}\{u,v\}$ 上直接计算行列式，得到

$$
\det D_c=-c\left(1-|\langle u,v\rangle|^2\right)<0.
$$

所以 $D_c$ 有一个严格正特征值和一个严格负特征值。记其正谱投影为 $P_c$。对于任意效应 $0\le F\le I$，

$$
\operatorname{tr}(FD_c)\le\operatorname{tr}(P_cD_c),
$$

而等号强制 $F=P_c$。事实上，在 $D_c$ 的正交特征基中，达到上界要求 $F$ 的正特征方向对角元为一、负特征方向对角元为零；$F\ge0$ 与 $I-F\ge0$ 随即使非对角元为零。这也给出

$$
\|D_c\|_1
=2\operatorname{tr}(P_cD_c)-\operatorname{tr}D_c.
$$

反设某个有限 POVM 对权重 $c$ 保持范数。把满足 $\operatorname{tr}(E_kD_c)>0$ 的结果集合记为 $S_c$，并令 $F_c=\sum_{k\in S_c}E_k$。则

$$
\sum_k|\operatorname{tr}(E_kD_c)|
=2\operatorname{tr}(F_cD_c)-\operatorname{tr}D_c.
$$

范数等号及最优效应的唯一性因此给出 $F_c=P_c$。迹为零的结果可以放入补集，上式仍精确成立。

若同一个 POVM 对 $c_1,c_2$ 都保持范数，按一个结果是否属于 $S_{c_1}$、$S_{c_2}$ 分成四组。相应四个效应记作 $G_{++},G_{+-},G_{-+},G_{--}$，满足

$$
\begin{aligned}
P_{c_1}&=G_{++}+G_{+-},&
I-P_{c_1}&=G_{-+}+G_{--},\\
P_{c_2}&=G_{++}+G_{-+},&
I-P_{c_2}&=G_{+-}+G_{--}.
\end{aligned}
$$

若 $0\le G\le P$ 且 $P$ 是正交投影，则 $PG=GP=G$；这是因为 $G$ 在 $\ker P$ 上的二次型为零，正性使该子空间包含于 $\ker G$。因此

$$
P_{c_1}P_{c_2}=G_{++}=P_{c_2}P_{c_1}.
$$

两个正谱投影可交换，意味着两个二阶 Hermitian 算子 $D_{c_1},D_{c_2}$ 可交换。然而

$$
[D_{c_1},D_{c_2}]=(c_2-c_1)[A,J]\ne0.
$$

最后的不等号来自 $c_1\ne c_2$ 以及两个不同且非正交的秩一投影不可交换，矛盾。故任何固定有限经典存储至少损失一个权重的判别量。

恒等量子存储保留 $A,J$ 本身，当然保持全部加权差的迹范数。对于存储前已知的最终权重 $c$，使用 $P_c,I-P_c$ 作二元测量，把正、负谱分别记入两个经典结果，所得绝对迹之和恰为 $\|D_c\|_1$。这里两种权重可以各自选择不同的存储测量；定理排除的是同一个经典存储同时无损。证毕。

**命题 34.3（两个后揭权重的精确经典和界）。** 在定义 34.1 中取

$$
A=|0\rangle\langle0|,
\qquad J=|+\rangle\langle+|,
\qquad |+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},
\qquad c_1=1,\quad c_2=\frac12.
$$

对任意有限经典存储，两个加权判别量的和满足精确界

$$
\sup_{\Phi\ \mathrm{classical}}
\left[L_\Phi(1)+L_\Phi(1/2)\right]=\frac52.
$$

一个二元投影测量已经达到该上界，而量子比特恒等存储给出

$$
L(1)+L(1/2)=\sqrt2+\frac{\sqrt5}{2}>\frac52.
$$

所以两问之和的经典损失至少为

$$
\frac{2\sqrt2+\sqrt5-5}{2}>0.
$$

这里比较的是陈述中两个加权迹范数的和，不把它称为两个不同先验成功概率的未加权和。

证明。用计算基写出

$$
D_1=\begin{pmatrix}1/2&-1/2\\-1/2&-1/2\end{pmatrix},
\qquad
D_{1/2}=\begin{pmatrix}0&-1/2\\-1/2&-1/2\end{pmatrix}.
$$

令

$$
B=D_1+D_{1/2}
=\begin{pmatrix}1/2&-1\\-1&-1\end{pmatrix},
\qquad
D_1-D_{1/2}=\frac12 A,
$$

并取

$$
Y=\begin{pmatrix}11/10&1/5\\1/5&7/5\end{pmatrix}.
$$

$B$ 的特征值为 $1,-3/2$。直接相乘有 $Y^2=B^2$，且 $Y$ 正定，因此 $Y=|B|$，特别地 $Y\ge B$、$Y\ge-B$。此外

$$
Y-\frac12A
=\begin{pmatrix}3/5&1/5\\1/5&7/5\end{pmatrix}>0,
$$

因为两个对角元为正、行列式为 $4/5>0$。由此也有 $Y\ge-\frac12A$。四种符号组合因此统一满足

$$
Y\ge sD_1+tD_{1/2},\qquad s,t\in\{-1,1\}.
$$

固定任意经典存储的 POVM $\{E_k\}$，对每个结果按两个实数 $\operatorname{tr}(E_kD_1)$、$\operatorname{tr}(E_kD_{1/2})$ 的符号选择 $s_k,t_k$；零值任取符号。正性给出

$$
\begin{aligned}
L_\Phi(1)+L_\Phi(1/2)
&=\sum_k\operatorname{tr}\bigl[E_k(s_kD_1+t_kD_{1/2})\bigr]\\
&\le\sum_k\operatorname{tr}(E_kY)
=\operatorname{tr}Y=\frac52.
\end{aligned}
$$

这个上界与经典结果的数量无关。取二元测量

$$
E_+=\frac15\begin{pmatrix}4&-2\\-2&1\end{pmatrix},
\qquad E_-=I-E_+.
$$

$E_+$ 是向量 $(2|0\rangle-|1\rangle)/\sqrt5$ 的秩一投影。四个输出差为

$$
\begin{aligned}
\operatorname{tr}(E_+D_1)&=\frac7{10},&
\operatorname{tr}(E_-D_1)&=-\frac7{10},\\
\operatorname{tr}(E_+D_{1/2})&=\frac3{10},&
\operatorname{tr}(E_-D_{1/2})&=-\frac45.
\end{aligned}
$$

故该测量分别得到 $7/5$ 与 $11/10$，两者之和正是 $5/2$，证明经典界的达到性。

两个加权秩一差的迹范数公式给出

$$
L(c)=\sqrt{(1+c)^2-2c}=\sqrt{1+c^2},
$$

于是量子恒等存储的两问之和为 $\sqrt2+\sqrt5/2$。为验证严格比较，$2\sqrt2>14/5$ 来自 $2>49/25$，而 $\sqrt5>11/5$ 来自 $5>121/25$；两式相加得 $2\sqrt2+\sqrt5>5$。这同时证明正损失的陈述。证毕。

<a id="entry-109"></a>

## 追加锚（新终端）

<a id="section-35"></a>

## 35. 两种后揭权重的全参数经典最优值与三结果测量

**定理 35.1（两个后揭权重的有限候选精确公式）。** 沿用定义 34.1 的固定存储任务，设两个候选是不同且非正交的纯量子比特态。记

$$
r=|\langle u,v\rangle|^2\in(0,1),
\qquad c_1,c_2>0,\quad c_1\ne c_2,
$$

$$
C=c_1+c_2,\qquad t=|c_1-c_2|,\qquad 0<t<C,
\qquad \nu=1-r.
$$

共同酉变换和向量代表相位允许取

$$
A=\begin{pmatrix}1&0\\0&0\end{pmatrix},
\qquad
J=\begin{pmatrix}r&\sqrt{r\nu}\\\sqrt{r\nu}&\nu\end{pmatrix}.
$$

定义

$$
B=CA-2J,
\qquad q=\|B\|_1=\sqrt{(C+2)^2-8Cr},
$$

并记所有有限经典存储上的最优和为

$$
V(C,t,r)=\sup_{\Phi\ \mathrm{classical}}
\bigl[L_\Phi(c_1)+L_\Phi(c_2)\bigr].
$$

第一参数域有简单精确公式：

$$
t\le\frac{Cq}{C+2}
\quad\Longrightarrow\quad V(C,t,r)=q.
$$

此时测量 $B$ 的正负谱投影即可达到。对其余参数域，以下三个显式矩阵给出完整精确公式。令

$$
Y_+=\frac{B+tA+|B-tA|}{2},
\qquad
Y_-=\frac{-B+tA+|B+tA|}{2}.
$$

再令

$$
k=\sqrt{\frac r\nu},
\qquad h=\sqrt{\frac{C^2-t^2}{2C\nu}},
\qquad w=k-h,
\qquad y=\frac{2C\nu}{t},
$$

$$
Y_3=\begin{pmatrix}t+yw^2&yw\\yw&y\end{pmatrix},
\qquad
R_3=\operatorname{tr}Y_3
=\frac{C(C+2)-2\sqrt{2Cr(C^2-t^2)}}{t}.
$$

定义候选值

$$
R_+=\begin{cases}
\operatorname{tr}Y_+,&Y_++B\ge0,\\
+\infty,&\text{否则},
\end{cases}
\qquad
R_-=\begin{cases}
\operatorname{tr}Y_-,&Y_--B\ge0,\\
+\infty,&\text{否则}.
\end{cases}
$$

则在 $t>Cq/(C+2)$ 时，

$$
\boxed{V(C,t,r)=\min\{R_+,R_-,R_3\}.}
$$

这里的可行性检验只是两个显式二阶 Hermitian 矩阵的半正定检验，等价于其迹与行列式均非负，不含连续优化。全部矩阵绝对值也可直接写成根式：对 $\lambda>0$，

$$
Q_\lambda=\sqrt{(\lambda+2)^2-8\lambda r},
$$

$$
|\lambda A-2J|
=\frac{(\lambda-2)(\lambda A-2J)+4\lambda\nu I}{Q_\lambda}.
$$

特别地，若 $c_{\rm hi}=(C+t)/2$、$c_{\rm lo}=(C-t)/2$，两个二结果候选矩阵的迹为（是否保留仍由上述可行性检验决定）

$$
\operatorname{tr}Y_+=c_{\rm hi}-1+L(c_{\rm lo}),
\qquad
\operatorname{tr}Y_-=1-c_{\rm lo}+L(c_{\rm hi}),
$$

$$
L(c)=\sqrt{(1+c)^2-4cr}.
$$

证明。不妨交换权重使 $c_1>c_2$。对任一 POVM 结果，两个带符号的迹之差是 $t\operatorname{tr}(E A)\ge0$。把原来的四种符号组合归并后，目标可以等价写成三结果优化

$$
\max_{E_+,E_-,E_0\ge0\,,\ E_++E_-+E_0=I}
\operatorname{tr}(E_+B)-\operatorname{tr}(E_-B)
+t\operatorname{tr}(E_0A).
$$

其理由也可不依赖零迹的符号约定：对每个原结果，两个绝对值之和等于对 $B,-B,tA,-tA$ 四种系数矩阵取最大迹；$tA\ge-tA$ 使第四项冗余。选择一个达到最大值的标签并合并同标签结果，得到三结果 POVM。反过来，对任一三结果 POVM，原绝对值目标至少为所示线性目标，故两个最优值相等。结果为零时任取一个达到最大值的标签即可。

这个三结果优化的对偶为

$$
\min\operatorname{tr}Y,
\qquad Y\ge B,\quad Y\ge-B,\quad Y\ge tA.
$$

原问题的可行集紧，且 $E_+=E_-=E_0=I/3$ 严格可行；对偶取足够大的正数乘 $I$ 也严格可行。因此 Slater 强对偶成立，两边最优值都达到。所有系数矩阵都为实矩阵，对任一可行矩阵及其复共轭取平均，保持可行性和目标，所以原、对偶最优解都可取实对称。对最优解有互补松弛

$$
(Y-B)E_+=0,
\qquad (Y+B)E_-=0,
\qquad (Y-tA)E_0=0.
$$

先考虑仅有前两项约束时的唯一最小迹解 $Y_0=|B|$，其迹为 $q$。$B$ 的行列式是 $-2C\nu<0$，故 $|B|$ 正定。由二阶矩阵绝对值公式，

$$
\langle u,|B|^{-1}u\rangle=\frac{C+2}{Cq}.
$$

令 $z_0=|B|^{-1/2}u$。对正定矩阵作合同变换，$|B|\ge tA$ 等价于

$$
I\ge t|z_0\rangle\langle z_0|,
$$

也就是 $t(C+2)/(Cq)\le1$。这证明 $Y_0$ 的可行域恰为所列第一参数域。测量 $B$ 的谱投影使两个结果上的 $B$ 迹绝对值之和为 $q$；原目标逐结果不小于该和，而可行 $Y_0$ 又给出上界 $q$，所以这一测量达到原目标 $q$。

以下证明剩余候选穷尽最优值。对任意可行 $Y$，三个差矩阵 $Y-B,Y+B,Y-tA$ 都不可能为零：前两种会要求不定矩阵 $B$ 或 $-B$ 半正定；第三种会要求 $tA\ge-B$，但在 $u^\perp$ 上左端为零、右端二次型为 $2\nu>0$。因此，每个奇异差矩阵都恰为秩一。

一个最优 POVM 不可能只有一个非零效应，否则该效应为 $I$，互补松弛会迫使对应差矩阵为零。若它恰有两个非零效应，互补松弛使它们的秩均至多为一；两个非零正秩一矩阵相加为 $I$，必为一对互补正交投影。它们于是达到相应两个系数矩阵的二元最优值。

对任意这里出现的二矩阵 $X_i,X_j$，差 $X_i-X_j$ 均可逆不定。二元最优效应是该差的唯一正谱投影，相应唯一最小迹上界是

$$
Y_{ij}=\frac{X_i+X_j+|X_i-X_j|}{2}.
$$

唯一性也由互补松弛直接得到：两个互补谱投影已固定，等式 $Y E_i=X_iE_i$、$Y E_j=X_jE_j$ 唯一确定 $Y$。所以两结果情形只能产生 $Y_0,Y_+,Y_-$ 中的一个；它还必须满足第三项约束。$Y_+$ 和 $Y_-$ 的剩余约束正是陈述中的两个可行性检验。

若最优 POVM 的三个效应均非零，则三个差矩阵都必须奇异。写

$$
Y=\begin{pmatrix}x&z\\z&y\end{pmatrix}.
$$

对 $\det(Y-B)=\det(Y+B)=\det(Y-tA)=0$ 展开，有

$$
\det Y=2C\nu,
\qquad y=\frac{2C\nu}{t},
\qquad x=t+\frac{z^2}{y}.
$$

剩下的线性混合项等式是

$$
y(C-2r)-2\nu x+4\sqrt{r\nu}\,z=0.
$$

令 $w=z/y$，化简得到

$$
(w-k)^2=h^2.
$$

所以两个三重接触候选分别为 $w=k-h$ 和 $w=k+h$。它们都可行：$Y-tA=y(w,1)^{\mathsf T}(w,1)$ 半正定，而 $Y-B,Y+B$ 的行列式均为零，右下角分别为

$$
2\nu\left(\frac Ct+1\right)>0,
\qquad
2\nu\left(\frac Ct-1\right)>0.
$$

二者因此都是半正定矩阵。由于 $k,h>0$，$w=k-h$ 的迹严格小于 $w=k+h$ 的迹，故高迹候选不可能最优；低迹候选就是 $Y_3$。

这样，至少一个最优解属于所列有限候选集合，而集合中的每个保留候选都可行。在第二参数域 $Y_0$ 已不可行，故精确最优值就是三个剩余候选迹的最小值。矩阵绝对值公式来自两个异号特征值上的线性插值；代入 $\lambda=C,C-t,C+t$ 即得陈述中的全部根式。证毕。

**命题 35.2（达到测量及三结果必要的参数例）。** 定理 35.1 中，若最小值由可行的 $Y_+$ 达到，测量 $B-tA=2(c_{\rm lo}A-J)$ 的正负谱投影即可达到；若由 $Y_-$ 达到，测量 $B+tA=2(c_{\rm hi}A-J)$ 的正负谱投影即可达到。

若 $Y_3$ 最优，其三结果达到测量可以显式写出。对二阶矩阵记 $\operatorname{adj}$ 为伴随矩阵，令

$$
S_\alpha=\frac{k}{yh},
\qquad d_\alpha=\frac{w}{2\nu h},
\qquad
\alpha_0=\frac{2Ck-h(C+2)}{2\nu ht},
$$

$$
\alpha_+=\frac{S_\alpha-\alpha_0-d_\alpha}{2},
\qquad
\alpha_-=\frac{S_\alpha-\alpha_0+d_\alpha}{2}.
$$

则

$$
E_+=\alpha_+\operatorname{adj}(Y_3-B),
\quad
E_-=\alpha_-\operatorname{adj}(Y_3+B),
\quad
E_0=\alpha_0\operatorname{adj}(Y_3-tA)
$$

是达到测量。当 $Y_3$ 最优时，这三个系数必非负；若只把 $Y_3$ 当作可行上界，不能省略这项非负性要求。特别地，$\alpha_0\ge0$ 恰好对应 $t\ge Cq/(C+2)$，但这一个条件本身不保证其余两个系数非负。

取

$$
C=2,\qquad t=1,\qquad r=\frac9{10},
$$

即权重为 $3/2,1/2$，则精确最优值是

$$
V=8-\frac{6\sqrt{30}}5.
$$

三个系数恰为

$$
\alpha_0=4\sqrt{30}-20,
\qquad
\alpha_+=\frac{25}{2}-\frac{9\sqrt{30}}4,
\qquad
\alpha_-=\frac{15}{2}-\frac{5\sqrt{30}}4,
$$

均严格为正。这个例子的最优经典测量需要至少三个非零结果；两个结果不能达到最优值。

证明。二结果候选的测量达到对应两项线性目标；第三项对偶约束已经验证可行，所以原绝对值目标也必须等于该候选迹。

对三结果式，三个伴随矩阵都是非零正秩一矩阵，分别支撑于对应差矩阵的核。把 $E_++E_-+E_0=I$ 的三个实矩阵坐标展开，得到唯一解

$$
\alpha_++\alpha_-+\alpha_0=\frac{k}{yh},
\qquad
\alpha_--\alpha_+=\frac{w}{2\nu h},
\qquad
\alpha_0=\frac{2Ck-h(C+2)}{2\nu ht}.
$$

这里 $k,y,h,\nu,t$ 全部为正。更明确地，把三个伴随矩阵依次按 $(11,12,22)$ 坐标写成三列，其行列式为

$$
-4t\nu yh=-8C\nu^2h\ne0,
$$

所以解确实唯一。若系数非负，这些效应组成 POVM 并逐项满足互补松弛，直接给出目标 $\operatorname{tr}Y_3$。反过来，若 $Y_3$ 最优，强对偶保证存在最优 POVM；其每项都支撑于相应一维核，只能是所写伴随矩阵的非负倍数。唯一性迫使其系数正是上述公式。这证明最优时的非负性与达到构造。

$\alpha_0$ 的阈值关系通过对 $h\le2Ck/(C+2)$ 平方并代入定义得到。具体例中，$5<\sqrt{30}<50/9<6$，所以三个系数都严格为正；代入 $R_3$ 得到所示精确值。该正系数 POVM 已达到可行对偶值，因而最优。任何其他最优 POVM 按三种系数矩阵分组后，都必须满足同一组互补松弛与完整性方程，因此三个组的系数也都是上述严格正数。只有两个非零原结果的测量至多产生两个非空组，不能满足这一要求。这证明三结果的必要性。

所用任意 Hermitian 测量奖励的 POVM 优化及其对偶，见 Watrous，*The Theory of Quantum Information*，[§3.1.2，式 (3.33)–(3.42)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)；同书定理 1.18 与命题 1.19 给出本证明所用的严格可行性、强对偶及互补松弛。这里的有限候选公式针对两种已知可能权重、存储后才揭示实际选择的任务，不把最终采用的权重在存储前已知时的单个 Helstrom 测量等同于对两问同时最优。

同一任务也可写成测量后揭示信息的二态辨别。令子系综标签为 $i=1,2$，其概率为 $\pi_i=(1+c_i)/(C+2)$，标签内部的 $A,J$ 先验分别为 $c_i/(1+c_i)$ 与 $1/(1+c_i)$。只在经典存储结束后揭示 $i$，则该存储及随后最优猜测的平均成功概率恰为

$$
p_{\rm guess}^{\Phi}
=\frac12+\frac{L_\Phi(c_1)+L_\Phi(c_2)}{2(C+2)}.
$$

因此本节优化与这个系综的后信息辨别只差固定正仿射变换。该一般框架见 Carmeli、Heinosaari、Toigo，[*State discrimination with post-measurement information and incompatibility of quantum measurements*（2018），§II.1、定理 1–2](https://arxiv.org/abs/1804.09693)。其定理 1 将事前与事后揭示信息时的最优值相同，刻画为存在兼容的各子系综最优测量；两个候选密度算子可以在不同子系综中重复出现，子系综标签仍互不混淆。这里的权重归一化与该映射明确保留了信息揭示的时点。证毕。

<a id="entry-111"></a>

## 追加锚（新终端）

<a id="section-36"></a>

## 36. 任意有限个后揭权重的三标签经典最优存储

**定理 36.1（有限权重表的三结果达到界）。** 沿用定义 34.1 的固定存储任务。允许 $A,J$ 为任意两个量子比特密度矩阵，即

$$
A,J\in\mathbb C^{2\times2},\qquad A,J\ge0,
\qquad \operatorname{tr}A=\operatorname{tr}J=1,
$$

并预先给定任意有限个正权重

$$
m\ge1,\qquad 0<c_1<c_2<\cdots<c_m.
$$

共同存储通道可以依赖 $A,J$ 和整个权重表，但必须在实际权重揭示前固定。对任意有限经典输出通道 $\Phi$，记

$$
L_\Phi(c)=\|c\Phi(A)-\Phi(J)\|_1,
\qquad
V_m=\sup_{\Phi\ \mathrm{classical}}\sum_{j=1}^m L_\Phi(c_j).
$$

这里优化的是所写范数之和；把某个权重的读数换算为定义 34.1 的判别成功率时，仍须使用该权重对应的 $1+c_j$ 分母。

对 $k=0,\ldots,m$ 定义 Hermitian 奖励矩阵

$$
G_k=
\left(\sum_{j=k+1}^m c_j-\sum_{j=1}^k c_j\right)A
+(2k-m)J,
$$

其中空和为零。则

$$
\boxed{
V_m=
\max_{\substack{E_0,\ldots,E_m\ge0\\\sum_{k=0}^m E_k=I}}
\sum_{k=0}^m\operatorname{tr}(E_kG_k)
=\min_{\substack{Y=Y^\dagger\\Y\ge G_k\ (0\le k\le m)}}
\operatorname{tr}Y.
}
$$

两个最优值均达到，并且存在一组达到原范数总分 $V_m$ 的 POVM，其非零效应数至多为

$$
\boxed{\min\{m+1,3\}.}
$$

因此，无论这张有限权重表有多少项，最优经典存储总能只保留至多三个输出标签。权重揭示后再根据存储标签作相应的二元决策。

证明。先核对从任意结果数到有限奖励表的归约。对一个任意 POVM 效应 $E\ge0$，令

$$
a=\operatorname{tr}(EA)\ge0,\qquad
b=\operatorname{tr}(EJ)\ge0.
$$

序列 $c_ja-b$ 随 $j$ 不减。因此可以选择一个 $k\in\{0,\ldots,m\}$，使 $j\le k$ 时 $c_ja-b\le0$，$j>k$ 时 $c_ja-b\ge0$。零值可以置于分界的任一侧；若 $a=0$，取 $k=m$ 即可，不需除以 $a$。于是

$$
\sum_{j=1}^m|c_ja-b|
=-\sum_{j=1}^k(c_ja-b)+\sum_{j=k+1}^m(c_ja-b)
=\operatorname{tr}(EG_k).
$$

任何其他分界给出的带符号和都不超过绝对值之和，所以逐效应恒有

$$
\sum_{j=1}^m\bigl|\operatorname{tr}(E(c_jA-J))\bigr|
=\max_{0\le k\le m}\operatorname{tr}(EG_k).
$$

给定任意有限 POVM $(M_\ell)_\ell$，为每个结果选择一个达到上述最大值的标签 $k(\ell)$，然后令

$$
E_k=\sum_{\ell:\,k(\ell)=k}M_\ell.
$$

这些效应组成 $m+1$ 标签的 POVM，其线性奖励恰等于原 POVM 的范数总分。因此，原问题在任意有限结果数上的上确界不超过所列线性奖励最大值。反过来，对任一这样的 $(E_k)$，逐效应的绝对值之和都不小于所选择的第 $k$ 项奖励，故其原范数总分不小于线性奖励。这给出反向不等式，两个最优值相等。

线性奖励的可行集是有限维紧集：各 $E_k$ 满足 $0\le E_k\le I$，完整性与正性条件均闭。连续目标因而达到最大值。其半正定对偶就是陈述中的 $Y\ge G_k$；原问题取 $E_k=I/(m+1)$ 严格可行，对偶取足够大的正数乘 $I$ 也严格可行。Slater 强对偶给出两者值相等及对偶最优值达到。

现在证明三个非零效应足够。先用共同酉变换将 $A$ 对角化，再施加保持 $A$ 对角的对角相位变换，使 $J$ 的非对角元变为实数；若该元为零，则无需第二步。即使 $A$ 简并，这个操作也成立。因此 $A,J$ 及全部 $G_k$ 都可取实对称矩阵。对一个最优 POVM 的每项作

$$
E_k\longmapsto\frac{E_k+\overline{E_k}}2,
$$

正性与完整性保持。由于 $G_k$ 实对称，$\operatorname{tr}(E_kG_k)$ 也保持，所以存在实对称最优 POVM。

记其非零效应的指标集为 $\mathcal I$。实对称二阶矩阵构成三维实向量空间。若 $|\mathcal I|>3$，则存在不全为零的实数 $(a_k)_{k\in\mathcal I}$，使

$$
\sum_{k\in\mathcal I}a_kE_k=0.
$$

每个非零正效应的迹严格为正。对该等式取迹可知，系数 $a_k$ 必须既有正数也有负数。把系数在 $\mathcal I$ 外延拓为零，并选择

$$
0<\varepsilon<\frac1{\max_{k\in\mathcal I}|a_k|}.
$$

则两组

$$
E_k^{\pm}=(1\pm\varepsilon a_k)E_k
$$

都为合法 POVM。令

$$
\Delta=\sum_{k\in\mathcal I}a_k\operatorname{tr}(E_kG_k).
$$

两组线性奖励分别为 $V_m+\varepsilon\Delta$ 与 $V_m-\varepsilon\Delta$。最优性要求两者都不超过 $V_m$，故 $\Delta=0$。

沿同一方向走到

$$
s_* =\min_{k:\,a_k<0}\frac{-1}{a_k}>0,
\qquad
\widetilde E_k=(1+s_*a_k)E_k.
$$

此时全部系数 $1+s_*a_k$ 非负，至少一个原非零效应变为零；矩阵和仍为 $I$，奖励仍为 $V_m+s_*\Delta=V_m$。这一步不要求效应为秩一。每次至少消去一个非零效应，有限次重复后便得到至多三个非零效应的最优奖励 POVM。

最后把这组 POVM 用作经典存储。其原范数总分不小于 $V_m$，又由 $V_m$ 的定义不大于 $V_m$，所以原目标也达到。删去零效应后，通道可写为

$$
\Phi_*(\rho)=\sum_{\ell=1}^{n_*}
\operatorname{tr}(E_\ell^*\rho)|\ell\rangle\langle\ell|,
\qquad n_*\le\min\{m+1,3\}.
$$

所用线性依赖扰动是标准 POVM 极点方法，见 D'Ariano、Lo Presti 与 Perinotti，*Classical randomness in quantum measurements*，[推论 7 及其证明](https://arxiv.org/abs/quant-ph/0408115)。实对称空间的 $d(d+1)/2$ 维数界也用于实态系综的可访问信息优化，见 Sasaki 等，*Accessible information and optimal strategies for real symmetrical quantum sources*，[引理 5](https://arxiv.org/abs/quant-ph/9812062)；该文研究的是 Shannon 互信息，上面的奖励归约与保值消去步骤直接处理本节的范数总分。证毕。

**推论 36.2（三标签统一界的锐性与纯态量子差距）。** 对定理 36.1 的全部候选对与有限权重表，统一的三标签上界不能改成两个。进一步，若

$$
A=|u\rangle\langle u|,\qquad J=|v\rangle\langle v|,
\qquad \|u\|=\|v\|=1,
\qquad 0<|\langle u,v\rangle|^2<1,
$$

且 $m\ge2$，则仍有严格差距

$$
V_m<\sum_{j=1}^m\|c_jA-J\|_1.
$$

证明。命题 35.2 中

$$
m=2,\qquad c_1=\frac12,\quad c_2=\frac32,
\qquad |\langle u,v\rangle|^2=\frac9{10}
$$

的最优经典总分为 $8-6\sqrt{30}/5$，且任一达到测量都至少有三个非零结果。它属于本节任务，故排除了对全部有限权重表适用的二标签上界。

对于所述纯态候选的严格差距，经典测量的迹范数收缩性逐项给出

$$
L_\Phi(c_j)\le\|c_jA-J\|_1.
$$

若总和取等，定理 36.1 保证存在达到该总和的有限经典存储，且每一项都必须取等。任选两个不同权重即与定理 34.2 矛盾。因此总和严格小于量子原值。恒等量子存储则同时保留右端各项。

这里的三标签计数只针对这一次固定存储后留下的经典输出，保证给定权重表上的最佳经典总分。所用测量可以随权重表改变；结论既不要求保留各个权重的量子最优值，也不给此前多阶段仪器、控制器运行存储或完整历史档案设定三标签上界。证毕。

<a id="entry-113"></a>

## 追加锚（新终端）

<a id="section-37"></a>

## 37. 混合量子比特后揭权重的同时无损分类

**定理 37.1（有限权重表的逐项无损条件）。** 沿用第 36 节的固定存储任务，设 $A,J$ 为任意两个量子比特密度矩阵，且

$$
m\ge1,\qquad 0<c_1<\cdots<c_m.
$$

记

$$
D_c=cA-J,\qquad
L(c)=\|D_c\|_1,\qquad
L_\Phi(c)=\|\Phi(D_c)\|_1,
$$

并定义不定权重集合及其大小

$$
\mathcal I=\{c_j:\det D_{c_j}<0\},\qquad n=|\mathcal I|.
$$

这里“不定”表示 $D_c$ 有一个严格正特征值和一个严格负特征值。行列式为零的权重不计入 $\mathcal I$。

存在同一个有限经典存储 $\Phi$，使

$$
L_\Phi(c_j)=L(c_j)\qquad(j=1,\ldots,m),
$$

当且仅当

$$
\boxed{[A,J]=0\quad\text{或}\quad n\le1.}
$$

证明。先处理不在 $\mathcal I$ 中的权重。二阶 Hermitian 矩阵的特征值为实数，行列式非负意味着它们同号或至少一个为零。因此 $D_c$ 半正定或半负定，且

$$
\|D_c\|_1=|\operatorname{tr}D_c|=|c-1|.
$$

任意 CPTP 映射都保持半定性与迹，故对这样的权重，任意存储自动满足

$$
\|\Phi(D_c)\|_1=|c-1|=\|D_c\|_1.
$$

特别地，$\det D_c=0$ 的端点不产生额外限制。若 $n=0$，只有一个效应 $I$ 的测量已经逐项无损；若 $n=1$，测量唯一不定矩阵的正、负谱投影即可，其他权重的等号自动保持。若 $[A,J]=0$，则共同本征基上的二元投影测量保持所有 $D_c$ 的谱读数，因而同时保持任意正权重的迹范数。这证明充分性。

下面证明必要性。设 $D_c$ 不定，写为

$$
D_c=\lambda_+P_c-\lambda_-(I-P_c),\qquad
\lambda_+,\lambda_->0,
$$

其中 $P_c$ 是秩一正谱投影。对任意效应 $E\ge0$，令

$$
x_E=\lambda_+\operatorname{tr}(EP_c),\qquad
y_E=\lambda_-\operatorname{tr}(E(I-P_c)).
$$

两者非负，所以 $|x_E-y_E|\le x_E+y_E$，等号当且仅当至少一项为零。若一个有限 POVM $(E_\ell)_\ell$ 保持 $\|D_c\|_1$，则

$$
\sum_\ell|x_{E_\ell}-y_{E_\ell}|
=\lambda_++\lambda_-
=\sum_\ell(x_{E_\ell}+y_{E_\ell}).
$$

每项的损失非负，总损失为零强制逐项取等。由正性，$\operatorname{tr}(EP)=0$ 对秩一投影 $P$ 意味着 $E$ 消去 $\operatorname{ran}P$：若 $P=|v\rangle\langle v|$，则 $\langle v,Ev\rangle=\|E^{1/2}v\|^2=0$。因此每个非零效应必为下列两种形式之一：

$$
E_\ell=\alpha_\ell P_c\quad\text{或}\quad
E_\ell=\beta_\ell(I-P_c),\qquad
\alpha_\ell,\beta_\ell>0.
$$

也就是说，不定权重的范数等号要求存储测量细分其唯一的二元谱测量。

若同一个 POVM 也对另一个不定权重 $d\ne c$ 保持等号，那么每个非零效应还必须为 $P_d$ 或 $I-P_d$ 的正倍数。取任意一个非零效应，比较其一维值域可知

$$
P_d=P_c\quad\text{或}\quad P_d=I-P_c.
$$

两个谱投影可交换，故 $D_c,D_d$ 可交换。但直接展开有

$$
[D_c,D_d]=(d-c)[A,J].
$$

由于 $d\ne c$，这要求 $[A,J]=0$。所以非对易候选对只要有两个不同的不定权重，就不存在逐项无损的有限经典存储。证毕。

**推论 37.2（最少输出资源及经典总分的等号条件）。** 对定理 37.1 的任务，最少非零经典输出标签数为

$$
\begin{cases}
1,&n=0,\\
2,&n\ge1\ \text{且}\ ([A,J]=0\ \text{或}\ n=1),\\
\text{不存在有限经典实现},&n\ge2\ \text{且}\ [A,J]\ne0.
\end{cases}
$$

若允许一般量子存储，逐项无损所需的最小输出 Hilbert 空间维数为

$$
\boxed{
 d_{\min}^{\mathrm{quantum}}=
 \begin{cases}
 1,&n=0,\\
 2,&n\ge1.
 \end{cases}
}
$$

第 36 节的最佳经典总分还满足

$$
\boxed{
V_m=\sum_{j=1}^mL(c_j)
\quad\Longleftrightarrow\quad
[A,J]=0\ \text{或}\ n\le1.
}
$$

因此，对非对易候选对及至少两个不定权重，有严格差距

$$
V_m<\sum_{j=1}^mL(c_j).
$$

证明。定理 37.1 已给出所有可行情形的一标签或二标签构造。若存在不定权重 $c$，其正、负谱均非零，因此

$$
\|D_c\|_1=\lambda_++\lambda_-
>|\lambda_+-\lambda_-|
=|c-1|.
$$

一标签经典通道对每个输入只输出概率一；更一般地，输出维数为一的 CPTP 映射只能输出唯一的密度矩阵。两者在权重 $c$ 上都只能留下 $|c-1|$，所以有不定权重时，一标签或一维量子输出均不足。二元测量达到经典可行情形的下界；量子比特恒等通道则保持 $A,J$ 本身，达到所有情形的二维量子上界。

最后，迹范数收缩性逐项给出 $L_\Phi(c_j)\le L(c_j)$。若定理 37.1 的条件成立，无损通道使总和取等。反过来，若 $V_m$ 等于量子总分，定理 36.1 保证该经典最大值由一个有限 POVM 达到。各项的非负损失之和为零，故同一个通道逐项无损，定理 37.1 的条件必须成立。它的补集因而给出所述严格不等式；这里没有声称一个与候选对及权重表无关的正差距常数。证毕。

**命题 37.3（同一个混合态对的三种权重表）。** 取

$$
A=\begin{pmatrix}3/4&0\\0&1/4\end{pmatrix},\qquad
J=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix}.
$$

两者均为满秩密度矩阵且不对易。对这个固定候选对，三种权重表的逐项无损资源如下：

| 预先给定的权重表 | 不定权重数 $n$ | 逐项无损的最少经典标签数 | 逐项无损的最小量子输出维数 |
| --- | ---: | --- | ---: |
| $(1/4,4)$ | $0$ | $1$ | $1$ |
| $(1/4,1,4)$ | $1$ | $2$ | $2$ |
| $(1,2)$ | $2$ | 不存在有限经典实现 | $2$ |

证明。$A,J$ 的特征值均为 $3/4,1/4$，所以都是满秩密度矩阵。直接相乘及计算行列式得到

$$
[A,J]=\begin{pmatrix}0&1/8\\-1/8&0\end{pmatrix}\ne0,
\qquad
\det(cA-J)=\frac{3c^2-8c+3}{16}.
$$

所以不定权重恰好位于开区间

$$
\left(\frac{4-\sqrt7}{3},\frac{4+\sqrt7}{3}\right).
$$

端点行列式为零，仍属半定情形。权重 $1/4,4$ 位于该区间外，$1,2$ 位于该区间内。三张表中的不定权重数因而分别为零、一、二；定理 37.1 与推论 37.2 给出所列资源结论。

这个例子说明，权重表的长度本身不决定同时无损的可行性。对不定区间之外的权重，先验已经使恒定决策达到最优；这些任务不要求存储保留候选态之间的区别。进入不定区间后，最优决策必须利用测量结果；同一个非对易候选对在两个不同的不定权重下要求不同且不兼容的二元谱测量。

上述结构是已知后测量信息判别与测量兼容性原理的量子比特特化。Carmeli、Heinosaari 与 Toigo 的 [Theorem 1](https://arxiv.org/html/1804.09693) 说明，有限个子系综的测量前、测量后信息判别最优值相等，当且仅当存在一组彼此兼容的各子系综最优测量；该结果允许一般混合态。对本节可明确取

$$
Z=m+\sum_{j=1}^m c_j,\qquad
q_j=\frac{1+c_j}{Z}>0,
$$

第 $j$ 个子系综的两个先验分别为 $c_j/(1+c_j)$ 与 $1/(1+c_j)$。用不同的标签 $(j,A)$、$(j,J)$ 区分子系综，即使密度矩阵在不同标签下重复，也符合该文的系综定义。由此

$$
p_{\mathrm{guess}}^{\mathrm{post}}
=\frac12+\frac{V_m}{2Z},\qquad
p_{\mathrm{guess}}^{\mathrm{prior}}
=\frac12+\frac{\sum_{j=1}^mL(c_j)}{2Z}.
$$

定理 37.1 将这项兼容性条件化为本任务可直接检查的行列式与对易子条件。这里的标签数和维数均只计算固定存储通道的输出；结论没有把一个量子比特等同于一位经典记录，也不对此前的控制器历史或多阶段协议总资源作相同计数。证毕。

<a id="entry-115"></a>

## 追加锚（新终端）

<a id="section-38"></a>

## 38. 高维无损存储的谱投影判据与输出维数

**定理 38.1（可逆加权差的相容性与最少输出资源）。** 把第 36 节的固定存储任务推广到任意有限维 Hilbert 空间 $\mathcal H$，记 $\dim\mathcal H=d\ge1$。设 $A,J$ 为该空间上的密度矩阵，预先给定

$$
m\ge1,\qquad 0<c_1<\cdots<c_m,
\qquad D_j=c_jA-J.
$$

假设每个 $D_j$ 都可逆，记 $P_j$ 为其正谱投影；允许 $P_j=0$ 或 $P_j=I$。所有候选输入使用同一个 CPTP 存储映射 $\Phi$，且该映射必须在实际权重揭示前固定。

存在有限经典输出存储使

$$
\|\Phi(D_j)\|_1=\|D_j\|_1\qquad(j=1,\ldots,m)
$$

当且仅当正谱投影族两两对易：

$$
\boxed{P_iP_j=P_jP_i\qquad(1\le i,j\le m).}
$$

在此相容条件成立时，对 $s=(s_1,\ldots,s_m)\in\{0,1\}^m$ 定义联合符号投影

$$
R_s=\prod_{j=1}^m\bigl[s_jP_j+(1-s_j)(I-P_j)\bigr],
\qquad
\mathcal S=\{s:R_s\ne0\},\qquad N=|\mathcal S|.
$$

这些乘积与排列次序无关。逐项无损所需的最少非零经典输出标签数，以及允许一般量子存储时的最小输出 Hilbert 空间维数，均恰为

$$
\boxed{n_{\min}^{\mathrm{classical}}=d_{\min}^{\mathrm{quantum}}=N.}
$$

这里的维数结论只针对上述相容情形。此外，在本节递增的正权重表下，相容投影必满足

$$
P_1\le P_2\le\cdots\le P_m,
\qquad 1\le N\le\min\{d,m+1\}.
$$

证明。先说明可逆性给出的等号刚性。对任意可逆 Hermitian 矩阵 $D$，写

$$
D=D_+-D_-,\qquad D_+,D_-\ge0,
$$

其中正、负部分支撑正交，正谱投影为 $P$。对 $0\le E\le I$ 有

$$
\operatorname{tr}(D_+)-\operatorname{tr}(ED)
=\operatorname{tr}((I-E)D_+)+\operatorname{tr}(ED_-)\ge0.
$$

右端为零当且仅当 $E$ 在 $D_+$ 的支撑上等于恒等、在 $D_-$ 的支撑上等于零。事实上，对正矩阵 $B,C$，$\operatorname{tr}(BC)=0$ 强制 $B^{1/2}C^{1/2}=0$；把它分别应用于两项即可。可逆性使这两个支撑的直和等于整个输入空间，故最优效应唯一，恰为 $P$。特别地，

$$
\max_{0\le E\le I}\operatorname{tr}(ED)
=\operatorname{tr}(D_+)
=\frac{\|D\|_1+\operatorname{tr}D}{2}.
$$

现在设 $\Phi$ 为任意逐项无损的有限维输出 CPTP 映射。对每个 $j$，在输出空间选择一个达到 $\Phi(D_j)$ 的上述最大值的效应 $F_j$。输出加权差可以有零特征值，这里只需选择一个最优效应，不要求它唯一。伴随映射 $\Phi^*$ 保单位且完全正，故 $\Phi^*(F_j)$ 是输入空间上的合法效应。迹保持与范数等号给出

$$
\operatorname{tr}(\Phi^*(F_j)D_j)
=\operatorname{tr}(F_j\Phi(D_j))
=\frac{\|D_j\|_1+\operatorname{tr}D_j}{2}.
$$

由输入最优效应的唯一性，得到关键算子等式

$$
\boxed{\Phi^*(F_j)=P_j\qquad(j=1,\ldots,m).}
$$

若输出是有限经典标签，设对应输入 POVM 为 $(E_\ell)_\ell$。输出加权差是对角矩阵，可以选择其严格正对角元集合的指示效应作为 $F_j$。因此每个 $P_j$ 都是同一 POVM 的结果合并：

$$
P_j=\sum_{\ell\in B_j}E_\ell.
$$

对任意两个指标 $i,j$，把标签按是否属于 $B_i,B_j$ 分成四组，所得效应记作 $G_{ab}$，$a,b\in\{0,1\}$。它们满足

$$
P_i=G_{11}+G_{10},\qquad
P_j=G_{11}+G_{01},\qquad
0\le G_{ab}\le P_i^{(a)},P_j^{(b)},
$$

其中 $P^{(1)}=P$、$P^{(0)}=I-P$。正效应被投影 $P$ 支配时，其支撑包含在 $\operatorname{ran}P$ 中，因而 $PE=EP=E$。据此

$$
P_iP_j=P_i(G_{11}+G_{01})=G_{11}
=P_jP_i.
$$

这证明经典逐项无损要求投影两两对易。

反过来，设全部 $P_j$ 两两对易。其联合投影 $(R_s)_{s\in\mathcal S}$ 两两正交，且和为 $I$。对每个 $j$，$R_s$ 的值域完全落在 $D_j$ 的正谱子空间或负谱子空间内，取决于 $s_j$。因此

$$
\bigl|\operatorname{tr}(R_sD_j)\bigr|
=(2s_j-1)\operatorname{tr}(R_sD_j).
$$

求和并使用 $\sum_s(2s_j-1)R_s=2P_j-I$，有

$$
\sum_{s\in\mathcal S}\bigl|\operatorname{tr}(R_sD_j)\bigr|
=\operatorname{tr}((2P_j-I)D_j)=\|D_j\|_1.
$$

于是通道

$$
\Phi_{\rm sign}(\rho)
=\sum_{s\in\mathcal S}\operatorname{tr}(R_s\rho)|s\rangle\langle s|
$$

同时保持所有加权差的迹范数。它有 $N$ 个非零经典标签，也给出输出维数为 $N$ 的一般量子存储上界。

为证明任意量子存储都不能使用更小的输出维数，对每个 $s\in\mathcal S$ 选择单位向量 $v_s\in\operatorname{ran}R_s$，并对任意逐项无损 CPTP 映射定义

$$
\rho_s=\Phi(|v_s\rangle\langle v_s|).
$$

由前面已证的拉回等式，

$$
\operatorname{tr}(F_j\rho_s)
=\langle v_s,P_jv_s\rangle=s_j.
$$

若密度矩阵 $\rho$ 对效应 $0\le F\le I$ 的期望为零，正性使 $\operatorname{supp}\rho\subseteq\ker F$；若期望为一，则对 $I-F$ 应用同一论证，得到 $\operatorname{supp}\rho\subseteq\ker(I-F)$。当 $s\ne t$ 时，至少存在一个 $j$ 使 $s_j\ne t_j$，故 $\rho_s$ 与 $\rho_t$ 分别支撑在 $F_j$ 的零和一本征空间内，二者正交。

这样，输出空间包含 $N$ 个两两正交且非零的支撑，因为每个 $\rho_s$ 的迹都为一。输出维数至少为 $N$。这里不要求输出效应族 $(F_j)$ 彼此对易；每对不同输出状态只需由其中一个效应确定地区分。向量 $v_s$ 是检验同一 CPTP 映射的数学测试输入，并未给原判别任务增添候选态。任意有限经典输出也属于一般量子输出，故同一下界适用于其标签数。结合构造，两种最少资源都等于 $N$。

最后核对投影嵌套。若 $i<j$，则

$$
D_j-D_i=(c_j-c_i)A\ge0.
$$

由于 $P_i,P_j$ 对易，若 $P_i(I-P_j)\ne0$，可在其值域中取单位向量 $v$。可逆性给出 $\langle v,D_iv\rangle>0$ 而 $\langle v,D_jv\rangle<0$，与上式矛盾。所以 $P_i\le P_j$。非零联合符号串只能由一段零接一段一组成，至多有 $m+1$ 种；两两正交的非零联合子空间数也不超过 $d$。这给出所列 $N$ 的上下界。

兼容最优测量与后揭信息判别的联系沿用 Carmeli、Heinosaari 与 Toigo 的 [Theorem 1](https://arxiv.org/html/1804.09693)，第 37 节给出的归一化映射同样适用于本节任意有限维候选。锐测量可共同测量时必须对易及其联合投影形式，见 Heinosaari、Reitzner 与 Stano，*Notes on Joint Measurability of Quantum Observables*，[附录 Proposition 8](https://arxiv.org/abs/0811.0783)。本节给出了这些标准兼容性原则在指定加权差任务上的直接证明，并用输出正交支撑计算最少资源。输入可逆性用于保证最优效应唯一；带有零特征值的加权差不在本定理范围内。证毕。

**命题 38.2（严格正定三维候选的非对易无损反例）。** 在 $\mathbb C^3$ 上取

$$
A=\frac1{12}\begin{pmatrix}
4&1&0\\
1&4&-1\\
0&-1&4
\end{pmatrix},
\qquad
J=\frac1{48}\begin{pmatrix}
8&3&0\\
3&16&-5\\
0&-5&24
\end{pmatrix},
$$

以及两个后揭权重

$$
c_1=\frac34,\qquad c_2=\frac54.
$$

这两个候选都是严格正定密度矩阵且 $[A,J]\ne0$。两个加权差 $D_1=c_1A-J$、$D_2=c_2A-J$ 均可逆不定，其正谱投影分别为

$$
P_1=\operatorname{diag}(1,0,0),\qquad
P_2=\operatorname{diag}(1,1,0).
$$

它们不同且严格嵌套。因此存在共同经典存储逐项无损，且其最少非零标签数与一般量子存储的最小输出维数都恰为三。两项被保持的量子范数均为

$$
\|D_1\|_1=\|D_2\|_1=\frac5{12}.
$$

证明。两个矩阵的迹都为一。它们的顺序主子式分别为

$$
A:\quad\frac13,\ \frac5{48},\ \frac7{216};
\qquad
J:\quad\frac16,\ \frac{119}{2304},\ \frac{83}{3456}.
$$

这些数均严格为正，Sylvester 判据给出严格正定性。直接相乘得到

$$
[A,J]=\frac1{288}
\begin{pmatrix}
0&4&-1\\
-4&0&-4\\
1&4&0
\end{pmatrix}\ne0.
$$

加权差为

$$
D_1=\frac1{24}
\begin{pmatrix}
2&0&0\\
0&-2&1\\
0&1&-6
\end{pmatrix},
\qquad
D_2=\frac1{24}
\begin{pmatrix}
6&1&0\\
1&2&0\\
0&0&-2
\end{pmatrix}.
$$

两个谱分别为

$$
\operatorname{spec}(D_1)
=\left\{\frac1{12},\frac{-4+\sqrt5}{24},\frac{-4-\sqrt5}{24}\right\},
$$

$$
\operatorname{spec}(D_2)
=\left\{-\frac1{12},\frac{4+\sqrt5}{24},\frac{4-\sqrt5}{24}\right\}.
$$

因 $0<\sqrt5<4$，它们都无零特征值，且分别有一个与两个正特征值。上述分块形式同时确定了陈述中的 $P_1,P_2$；按符号求特征值绝对值之和得到两项范数 $5/12$。

非零联合符号投影恰为

$$
R_{(1,1)}=|e_1\rangle\langle e_1|,\qquad
R_{(0,1)}=|e_2\rangle\langle e_2|,\qquad
R_{(0,0)}=|e_3\rangle\langle e_3|,
$$

而 $R_{(1,0)}=0$。定理 38.1 因而给出两种最少输出资源都为三。具体达到测量就是标准基上的三元投影测量；它在两个权重上的读数分别为

$$
\left(\frac1{12},-\frac1{12},-\frac14\right),
\qquad
\left(\frac14,\frac1{12},-\frac1{12}\right),
$$

各自的绝对值之和均为 $5/12$。

这个反例说明定理 37.1 的候选态对易判据具有二维限制。在二维不定情形，每个加权差都是恒等矩阵与其正谱投影的线性组合，正谱投影对易便迫使加权差对易。在三维，一个正谱或负谱子空间可以有二维；不同加权差在这些子空间内部仍能不对易，而选定判别任务的正负谱投影已经相容。这里三个经典标签保存的是两问所需的联合符号信息，定理并未要求保存候选态的全部量子结构。证毕。

<a id="entry-117"></a>

## 追加锚（新终端）

<a id="section-39"></a>

## 39. 两项不定判别量无损强制整个量子比特可恢复

**定理 39.1（两权重等号与全输入可恢复性）。** 设 $A,J$ 为量子比特密度矩阵，且

$$
[A,J]\ne0,\qquad c,d>0,\qquad c\ne d.
$$

记 $D_t=tA-J$，并要求两个加权差都严格不定：

$$
\det D_c<0,\qquad \det D_d<0.
$$

令 $\Phi:\mathcal L(\mathbb C^2)\to\mathcal L(\mathcal H_B)$ 为 CPTP 映射，其中输出空间 $\mathcal H_B$ 有限维。则

$$
\boxed{
\|\Phi(D_c)\|_1=\|D_c\|_1
\quad\text{且}\quad
\|\Phi(D_d)\|_1=\|D_d\|_1
\quad\Longleftrightarrow\quad
\exists\ \mathcal R\ \mathrm{CPTP},\quad
\mathcal R\circ\Phi=\operatorname{id}_{\mathcal L(\mathbb C^2)}.
}
$$

右端的恢复通道定义在整个 $\mathcal L(\mathcal H_B)$ 上，恢复所有量子比特输入；它是 $\Phi$ 的 CPTP 左逆，不要求 $\Phi$ 映满全部输出状态。

这些条件还等价于下面的正交等距正规形：存在整数 $r\ge1$、正数 $\lambda_1,\ldots,\lambda_r$ 及等距映射 $V_a:\mathbb C^2\to\mathcal H_B$，满足

$$
\sum_{a=1}^r\lambda_a=1,\qquad
V_a^\dagger V_b=\delta_{ab}I_2,
\qquad
\Phi(X)=\sum_{a=1}^r\lambda_aV_aXV_a^\dagger
\quad\text{对全部 }X\in\mathcal L(\mathbb C^2).
$$

特别地，$2r\le\dim\mathcal H_B$。定义

$$
\omega=\sum_{a=1}^r\lambda_a|a\rangle\langle a|,\qquad
W(|\psi\rangle\otimes|a\rangle)=V_a|\psi\rangle,
$$

则 $W:\mathbb C^2\otimes\mathbb C^r\to\mathcal H_B$ 是等距映射，且

$$
\boxed{\Phi(\rho)=W(\rho\otimes\omega)W^\dagger.}
$$

辅助态 $\omega$ 固定且与输入无关，可以是混合态。上述表达只占用输出空间中的一个子空间，不要求输出维数为偶数。

证明。先由两个范数等号推出正规形。对 $t\in\{c,d\}$，将输入加权差写成

$$
D_t=\mu_{t,+}P_t-\mu_{t,-}(I_2-P_t),\qquad
\mu_{t,+},\mu_{t,-}>0,
$$

其中 $P_t$ 为秩一正谱投影。令

$$
\rho_{t,+}=\Phi(P_t),\qquad
\rho_{t,-}=\Phi(I_2-P_t).
$$

两者均为输出密度矩阵。有限维输出上存在最优二元判别效应 $0\le F_t\le I_B$。对任意 Hermitian 矩阵 $H$，有

$$
\|H\|_1=2\max_{0\le F\le I}\operatorname{tr}(FH)-\operatorname{tr}H.
$$

应用于 $H=\Phi(D_t)$，再用范数等号和迹保持性，得到

$$
\operatorname{tr}\!\left[F_t
(\mu_{t,+}\rho_{t,+}-\mu_{t,-}\rho_{t,-})\right]
=\mu_{t,+}.
$$

等价地，

$$
\mu_{t,+}\bigl(1-\operatorname{tr}(F_t\rho_{t,+})\bigr)
+\mu_{t,-}\operatorname{tr}(F_t\rho_{t,-})=0.
$$

两项非负且两个系数严格为正，故

$$
\operatorname{tr}(F_t\rho_{t,+})=1,\qquad
\operatorname{tr}(F_t\rho_{t,-})=0.
$$

正性将这两个条件分别化为

$$
\operatorname{supp}\rho_{t,+}\subseteq\ker(I_B-F_t),\qquad
\operatorname{supp}\rho_{t,-}\subseteq\ker F_t.
$$

因此，$D_t$ 的两个纯本征输入经 $\Phi$ 后仍有正交支撑。

取 $\Phi$ 的任意有限 Kraus 表示

$$
\Phi(X)=\sum_{a=1}^N K_aXK_a^\dagger,\qquad
\sum_{a=1}^N K_a^\dagger K_a=I_2.
$$

若 $|t,+\rangle,|t,-\rangle$ 是 $P_t,I_2-P_t$ 的单位本征向量，则 $K_a|t,+\rangle$ 与 $K_b|t,-\rangle$ 分别落在上述正交支撑内。对任意 $a,b$，于是

$$
\langle t,+|K_a^\dagger K_b|t,-\rangle=0,\qquad
\langle t,-|K_a^\dagger K_b|t,+\rangle=0.
$$

所以 $K_a^\dagger K_b$ 在 $P_t$ 的本征基中对角；这个矩阵不必自伴，但两个非对角元都为零。

另一方面，

$$
[D_c,D_d]=(d-c)[A,J]\ne0.
$$

由于每个 $D_t$ 都是 $P_t$ 的非退化仿射函数，可知 $[P_c,P_d]\ne0$。一个二阶矩阵若在 $P_c$ 的本征基中对角，就可写为 $xI_2+yP_c$；若还与 $P_d$ 对易，则 $y[P_c,P_d]=0$，从而 $y=0$。因此存在复数 $\alpha_{ab}$，使

$$
\boxed{K_a^\dagger K_b=\alpha_{ab}I_2\qquad(1\le a,b\le N).}
$$

矩阵 $\alpha=(\alpha_{ab})$ 自伴且半正定。事实上，对任意 $z\in\mathbb C^N$，

$$
\left(\sum_a z_aK_a\right)^\dagger
\left(\sum_b z_bK_b\right)
=(z^\dagger\alpha z)I_2\ge0.
$$

迹保持性又给出 $\sum_a\alpha_{aa}=1$。选取酉矩阵 $U$ 使 $U^\dagger\alpha U$ 对角，并置 $L_b=\sum_aU_{ab}K_a$。这些算子仍表示同一个通道，且

$$
L_a^\dagger L_b=\delta_{ab}\lambda_aI_2,
\qquad \lambda_a\ge0,\qquad \sum_a\lambda_a=1.
$$

删去 $\lambda_a=0$ 的零算子，对剩余算子定义 $V_a=L_a/\sqrt{\lambda_a}$，即得到所述正交等距正规形。各 $V_a$ 的像空间两两正交且均为二维，故 $2r\le\dim\mathcal H_B$。由 $V_a^\dagger V_b=\delta_{ab}I_2$ 可直接核对 $W^\dagger W=I_2\otimes I_r$，以及固定辅助态表达。

现在由正规形构造恢复通道。令

$$
Q=\sum_{a=1}^rV_aV_a^\dagger,
$$

它是 $\Phi$ 所占用输出子空间的正交投影。任选一个量子比特密度矩阵 $\tau$，定义

$$
\boxed{
\mathcal R(X)=\sum_{a=1}^rV_a^\dagger XV_a
+\operatorname{tr}\bigl[(I_B-Q)X\bigr]\tau.
}
$$

第一项为 Kraus 形式的完全正映射，第二项为一个测量后制备固定态的完全正映射。两项的迹分别为 $\operatorname{tr}(QX)$ 与 $\operatorname{tr}((I_B-Q)X)$，故 $\mathcal R$ 保持迹，且定义覆盖整个输出空间。对任意量子比特输入矩阵 $X$，正交等距关系给出

$$
\mathcal R(\Phi(X))
=\sum_{a=1}^r\lambda_aX=X.
$$

最后，若已有 CPTP 左逆 $\mathcal R$，对任意 Hermitian 输入 $H$，迹范数收缩性给出

$$
\|H\|_1=\|\mathcal R(\Phi(H))\|_1
\le\|\Phi(H)\|_1\le\|H\|_1.
$$

所以 $\Phi$ 保持全部 Hermitian 输入的迹范数，特别地保持 $D_c,D_d$。这完成全部等价关系。由于恢复的是整个输入空间上的恒等通道，张量一个任意有限维参考系统后仍有恒等关系；恢复也保留输入与该参考系统的纠缠，不要求访问参考系统。

上面的 $K_a^\dagger K_b=\alpha_{ab}I_2$ 是以整个量子比特作为编码空间的标准 Knill–Laflamme 条件，见 Knill 与 Laflamme，*Theory of quantum error-correcting codes*，[Theorem 3.2 的式 (19)、(20) 及 Theorem 3.3](https://arxiv.org/html/quant-ph/9604034)。可恢复通道的正交等距及固定辅助态正规形也已有一般维数的结果，见 Nayak 与 Sen，*Invertible Quantum Operations and Perfect Encryption of Quantum States*，[Theorem 2.1 及其证明中的式 (2)、(3)](https://arxiv.org/html/quant-ph/0605041)。本节的两权重判据通过两个不兼容谱基的范数等号达到这些已有条件；它不把一般纠错条件或可恢复通道正规形另作新理论。证毕。

**推论 39.2（二维输出时必须是酉通道）。** 在定理 39.1 的非对易、两个不同严格不定权重假设下，若还要求 $\mathcal H_B=\mathbb C^2$，则

$$
\|\Phi(D_c)\|_1=\|D_c\|_1
\quad\text{且}\quad
\|\Phi(D_d)\|_1=\|D_d\|_1
\quad\Longleftrightarrow\quad
\exists\ U\ \mathrm{unitary},\quad
\Phi(X)=UXU^\dagger\ \text{对全部 }X.
$$

证明。定理 39.1 给出 $r\ge1$ 与 $2r\le2$，故 $r=1$、$\lambda_1=1$。唯一的等距映射 $V_1:\mathbb C^2\to\mathbb C^2$ 是酉矩阵，取 $U=V_1$ 即得结论。反向由酉共轭保持迹范数成立。

这里不是用两个标量读数重建一个未知量子态，而是要求同一个 CPTP 通道在两个指定判别任务上都保持量子最优值。严格不定性使每个等号要求保留一整组正交本征输入的可区分性；非对易性使这两组谱基不兼容，进而约束整个通道。结论中的有限输出、非对易、不同权重及两个严格不定条件均保留，不由第 37 节中半定权重的自动无损情形代替。证毕。

<a id="entry-119"></a>

## 追加锚（新终端）

<a id="section-40"></a>

## 40. 后揭两权重的经典损失底线与可达上界

**定理 40.1（两项严格不定任务的显式损失界）。** 设 $A,J$ 为量子比特密度矩阵，且

$$
[A,J]\ne0,\qquad c,d>0,\qquad c\ne d,
\qquad \det(cA-J)<0,\quad\det(dA-J)<0.
$$

对 $t\in\{c,d\}$，记

$$
D_t=tA-J,\qquad P_t=\mathbf 1_{(0,\infty)}(D_t),
\qquad S_t=2P_t-I_2,
$$

$$
a_t=\frac{t-1}{2},\qquad
b_t=\frac{\|D_t\|_1}{2},\qquad
\mu_t=b_t-|a_t|>0.
$$

于是 $D_t=a_tI_2+b_tS_t$，且 $\mu_t$ 是正、负特征值绝对值中的较小者。再记

$$
\kappa=2\operatorname{tr}(P_cP_d)-1,
\qquad \eta=|\kappa|\in[0,1),
$$

$$
M=\sqrt{\mu_c^2+\mu_d^2+2\mu_c\mu_d\eta},
$$

$$
\mathsf L=2(\mu_c+\mu_d-M),
\qquad
\mathsf U=2\min\{\mu_c,\mu_d,b_c(1-\eta),b_d(1-\eta)\}.
$$

令 $V$ 为在同一个有限经典存储上优化的范数总分，允许任意有限结果数：

$$
V=\max_{\Phi\ \mathrm{classical}}
\bigl(\|\Phi(D_c)\|_1+\|\Phi(D_d)\|_1\bigr),
\qquad
\Delta=\|D_c\|_1+\|D_d\|_1-V.
$$

最大值的存在性由定理 36.1 保证。则

$$
\boxed{0<\mathsf L\le\Delta\le\mathsf U.}
$$

上界 $\mathsf U$ 由两个明确的存储测量之一达到其所述损失：在 $P_c,I_2-P_c$ 与 $P_d,I_2-P_d$ 之间，预先选择总损失较小的一组，然后固定使用它。该选择依赖已知候选及完整权重表，不依赖后来才揭示的实际权重。

证明。首先，由 $[D_c,D_d]=(d-c)[A,J]\ne0$ 及量子比特的非退化谱分解，可知 $P_c,P_d$ 不对易。两个秩一投影对易当且仅当其值域相同或正交，所以 $0<\operatorname{tr}(P_cP_d)<1$，即 $\eta<1$。

固定任意有限 POVM $(E_\ell)_\ell$ 及其经典输出通道 $\Phi$。记它在权重 $t$ 上的损失为

$$
\delta_t=\|D_t\|_1-\|\Phi(D_t)\|_1.
$$

写 $\lambda_{t,+}=b_t+a_t>0$、$\lambda_{t,-}=b_t-a_t>0$。对固定 $t$，令

$$
p_\ell=\operatorname{tr}(E_\ell P_t),\qquad
q_\ell=\operatorname{tr}(E_\ell(I_2-P_t)).
$$

两组数非负且各自之和为一。经典输出的对角元为 $\lambda_{t,+}p_\ell-\lambda_{t,-}q_\ell$，所以

$$
\begin{aligned}
\delta_t
&=2\sum_\ell\min\{\lambda_{t,+}p_\ell,\lambda_{t,-}q_\ell\}\\
&\ge2\mu_t\sum_\ell\min\{p_\ell,q_\ell\}\\
&=\mu_t\left(2-\sum_\ell|p_\ell-q_\ell|\right)\\
&=\mu_t\bigl(2-\|\Phi(S_t)\|_1\bigr).
\end{aligned}
$$

剩下的辅助测量优化有一个精确值：

$$
\max_{\Phi\ \mathrm{classical}}
\bigl(\mu_c\|\Phi(S_c)\|_1+\mu_d\|\Phi(S_d)\|_1\bigr)=2M.
$$

为直接证明它，对 $\varepsilon,\zeta\in\{-1,1\}$ 定义四个奖励矩阵

$$
X_{\varepsilon,\zeta}
=\varepsilon\mu_cS_c+\zeta\mu_dS_d.
$$

两个无迹二阶矩阵满足

$$
S_c^2=S_d^2=I_2,
\qquad S_cS_d+S_dS_c=2\kappa I_2.
$$

第二式可将无迹二阶矩阵的恒等式 $X^2=\tfrac12\operatorname{tr}(X^2)I_2$ 应用于 $S_c+S_d$ 后得到，其中 $\operatorname{tr}(S_cS_d)=2\kappa$。

因此

$$
X_{\varepsilon,\zeta}^2
=\bigl(\mu_c^2+\mu_d^2+2\varepsilon\zeta\mu_c\mu_d\kappa\bigr)I_2,
\qquad MI_2\ge X_{\varepsilon,\zeta}.
$$

逐效应选择两个迹的符号，便有

$$
\begin{aligned}
&\mu_c\|\Phi(S_c)\|_1+\mu_d\|\Phi(S_d)\|_1\\
&=\sum_\ell\max_{\varepsilon,\zeta}
\operatorname{tr}(E_\ell X_{\varepsilon,\zeta})
\le\sum_\ell\operatorname{tr}(E_\ell MI_2)=2M.
\end{aligned}
$$

选择 $\varepsilon\zeta\kappa=|\kappa|$；若 $\kappa=0$，任选一个符号组合即可。对应矩阵 $X$ 无迹且有特征值 $M,-M$。测量它的正、负谱投影，并在两结果上分别采用奖励 $X,-X$，线性奖励之和恰为 $2M$。原绝对值目标不小于这组奖励，又受上面的 $2M$ 约束，故达到 $2M$。这证明辅助最优值，且二元谱测量足够。

将辅助上界代入两个单项损失估计，得到对每个有限经典存储都成立的

$$
\delta_c+\delta_d\ge2(\mu_c+\mu_d)-2M=\mathsf L.
$$

而

$$
(\mu_c+\mu_d)^2-M^2=2\mu_c\mu_d(1-\eta)>0,
$$

所以 $\mathsf L>0$；也可写成

$$
\mathsf L=
\frac{4\mu_c\mu_d(1-\eta)}{\mu_c+\mu_d+M}.
$$

现在给出实际测量的上界。选择 $P_c,I_2-P_c$ 时，权重 $c$ 的范数完全保持，而 $D_d$ 的两个输出对角元为

$$
a_d+b_d\kappa,\qquad a_d-b_d\kappa.
$$

利用 $|x+y|+|x-y|=2\max\{|x|,|y|\}$，这组测量在 $d$ 上的范数和损失分别为

$$
2\max\{|a_d|,b_d\eta\},
\qquad
2b_d-2\max\{|a_d|,b_d\eta\}
=2\min\{\mu_d,b_d(1-\eta)\}.
$$

交换 $c,d$，另一组谱测量的总损失为 $2\min\{\mu_c,b_c(1-\eta)\}$。选择其中较小者，所得实际总损失正好为 $\mathsf U$，因此最佳经典存储的损失 $\Delta\le\mathsf U$。结合此前对任意存储的下界，完成所列夹逼。

这两个界可以直接解释为容差限制。给定 $\epsilon_c,\epsilon_d\ge0$，若要求同一个经典存储满足 $\delta_c\le\epsilon_c$、$\delta_d\le\epsilon_d$，必要条件是

$$
\epsilon_c+\epsilon_d\ge\mathsf L.
$$

若只要求总损失不超过 $\epsilon$，则 $\epsilon<\mathsf L$ 不可行，而 $\epsilon\ge\mathsf U$ 由上述二元谱测量保证可行。中间区间的判定仍需实际最优值 $\Delta$。

按第 37 节的归一化，令

$$
Z=2+c+d,\qquad q_c=\frac{1+c}{Z},\qquad q_d=\frac{1+d}{Z},
$$

并在权重 $t$ 下使用条件先验 $t/(1+t),1/(1+t)$。权重揭示前保留量子输入的最佳平均成功率，与先作经典存储后再揭示权重的最佳平均成功率，分别为

$$
p_{\rm quantum}=\frac12+\frac{\|D_c\|_1+\|D_d\|_1}{2Z},
\qquad
p_{\rm classical}=\frac12+\frac{V}{2Z}.
$$

因此

$$
\frac{\mathsf L}{2Z}
\le p_{\rm quantum}-p_{\rm classical}
=\frac{\Delta}{2Z}
\le\frac{\mathsf U}{2Z}.
$$

沿满足本定理假设的参数序列，若 $\min\{\mu_c,\mu_d\}\to0$，或 $\min\{b_c,b_d\}(1-\eta)\to0$，上界立即给出 $\Delta\to0$。特别地，在 $\min\{b_c,b_d\}$ 有界时，$\eta\to1$ 足以使损失趋零。这些界依赖给定候选与权重，未给出跨参数的统一正损失常数。

辅助优化在 $\mu_c=\mu_d$ 时，对应 Carmeli、Heinosaari 与 Toigo，[§V.2，式 (27)](https://arxiv.org/html/1804.09693) 的两个等概率量子比特本征基：其后测量信息成功率为 $\tfrac12(1+\sqrt{(1+\eta)/2})$。一般正系数的辅助最优值由上面的四奖励证书直接证明。辅助值的精确性不使原损失下界自动精确，因为将两本征值绝对值同时替换为 $\mu_t$ 的步骤可以产生严格不等式。证毕。

**命题 40.2（混态例中的精确最优值与两个严格界）。** 取命题 37.3 的满秩候选

$$
A=\begin{pmatrix}3/4&0\\0&1/4\end{pmatrix},\qquad
J=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix},
\qquad c=1,\quad d=2.
$$

最佳经典范数总分及其相对量子总分的损失为

$$
\boxed{V=\frac{\sqrt{13}}2,\qquad
\Delta=\frac{\sqrt2+\sqrt5-\sqrt{13}}2.}
$$

定理 40.1 的两个界在此化为

$$
\mathsf L=
\frac{\sqrt2+\sqrt5-2-\sqrt{17-32/\sqrt5}}2,
\qquad
\mathsf U=\frac{\sqrt2-3/\sqrt5}{2},
$$

并满足严格关系

$$
\boxed{0<\mathsf L<\Delta<\mathsf U.}
$$

证明。命题 37.3 已核对候选不对易及两个权重都在严格不定区间。这里直接写出

$$
D_1=\frac14\begin{pmatrix}1&-1\\-1&-1\end{pmatrix},
\qquad
D_2=\begin{pmatrix}1&-1/4\\-1/4&0\end{pmatrix}.
$$

它们的迹范数分别为 $\sqrt2/2$ 与 $\sqrt5/2$；由 $S_t=(D_t-a_tI_2)/b_t$ 计算得到 $\operatorname{tr}(S_cS_d)=6/\sqrt{10}$。因此

$$
b_c=\mu_c=\frac{\sqrt2}{4},\qquad
b_d=\frac{\sqrt5}{4},\qquad
\mu_d=\frac{\sqrt5-2}{4},\qquad
\eta=\frac3{\sqrt{10}}.
$$

先计算最佳经典值。两个差矩阵之和与差为

$$
B=D_1+D_2=3A-2J
=\begin{pmatrix}5/4&-1/2\\-1/2&-1/4\end{pmatrix},
\qquad D_2-D_1=A\ge0.
$$

对任一效应 $E\ge0$，两个绝对迹之和等于在 $B,-B,A$ 三个奖励矩阵上取最大迹；第四种符号对应的 $-A$ 被 $A$ 支配。令

$$
Y=|B|=\frac1{4\sqrt{13}}
\begin{pmatrix}19&-4\\-4&7\end{pmatrix}.
$$

$B$ 的特征值为 $(2+\sqrt{13})/4$ 与 $(2-\sqrt{13})/4$；在这两个异号特征值上线性插值得 $|B|=(2B+9I_2/4)/\sqrt{13}$，即上面的矩阵。因此 $Y\ge B,-B$ 且 $\operatorname{tr}Y=\sqrt{13}/2$。另外

$$
Y-A=\frac1{4\sqrt{13}}
\begin{pmatrix}19-3\sqrt{13}&-4\\-4&7-\sqrt{13}\end{pmatrix}>0.
$$

其左上元为正，行列式的分子为 $156-40\sqrt{13}>0$；后一个严格不等式由 $39^2>100\cdot13$ 得到。因此 $Y$ 支配全部三个奖励，对任意有限 POVM 都给出

$$
\|\Phi(D_1)\|_1+\|\Phi(D_2)\|_1\le\operatorname{tr}Y=\frac{\sqrt{13}}2.
$$

达到这个界的测量是 $B$ 的二元谱测量。具体令

$$
T=\frac1{\sqrt{13}}\begin{pmatrix}3&-2\\-2&-3\end{pmatrix},
\qquad E_+=\frac{I_2+T}{2},\quad E_-=\frac{I_2-T}{2}.
$$

$T^2=I_2$，所以 $E_+,E_-$ 是互补投影。直接计算四个迹，得到

$$
\operatorname{tr}(E_\pm D_1)=\pm\frac5{4\sqrt{13}},
\qquad
\operatorname{tr}(E_\pm D_2)=\frac12\pm\frac2{\sqrt{13}}.
$$

因为 $4>\sqrt{13}$，第二组也一正一负。两个范数之和于是为

$$
\frac5{2\sqrt{13}}+\frac4{\sqrt{13}}=\frac{\sqrt{13}}2.
$$

这证明所列精确 $V$，从量子总分 $(\sqrt2+\sqrt5)/2$ 减去它即得 $\Delta$。

代入前面的 $\mu_c,\mu_d,\eta$，有

$$
M^2=\frac{17-32/\sqrt5}{16},
$$

因而得到陈述中的 $\mathsf L$。由于 $b_c<b_d$ 且

$$
b_d\eta=\frac3{4\sqrt2}>\frac12=|a_d|,
$$

上界四项中的最小者为 $b_c(1-\eta)$，所以 $\mathsf U=2b_c(1-\eta)=(\sqrt2-3/\sqrt5)/2$。

定理 40.1 已给出 $\mathsf L>0$。最后，$\Delta<\mathsf U$ 等价于

$$
\frac8{\sqrt5}<\sqrt{13},
$$

它由 $64<65$ 成立。另一方面，因为 $\sqrt{13}-2>0$，$\mathsf L<\Delta$ 等价于

$$
\sqrt{17-32/\sqrt5}>\sqrt{13}-2.
$$

两边平方后恰好得到同一个 $8/\sqrt5<\sqrt{13}$。这证明全部严格关系。此例的最佳二元测量采用 $D_1+D_2$ 的谱基，严格优于只在两个单项谱测量之间选择；同时原损失严格高于由辅助优化得到的下界。证毕。

<a id="entry-121"></a>

## 追加锚（新终端）

<a id="section-41"></a>

## 41. 判别谱投影生成的代数与最小存储维数

**定理 41.1（完整输出与免费经典标签的两种精确维数）。** 沿用定理 38.1 的有限维任务。设 $\dim\mathcal H=D\ge1$，$A,J$ 为输入密度矩阵，且

$$
m\ge1,\qquad 0<c_1<\cdots<c_m,\qquad
D_j=c_jA-J\ \text{均可逆}.
$$

令 $P_j=\mathbf 1_{(0,\infty)}(D_j)$ 为正谱投影，允许 $P_j=0$ 或 $I$。记它们生成的含单位有限维 $C^*$ 代数为

$$
\mathfrak A=C^*(I,P_1,\ldots,P_m)\subseteq\mathcal L(\mathcal H).
$$

选择该代数的标准分块表示

$$
\mathcal H\cong\bigoplus_{k=1}^s
\left(\mathbb C^{d_k}\otimes\mathbb C^{m_k}\right),\qquad
\mathfrak A\cong\bigoplus_{k=1}^s
\left(M_{d_k}(\mathbb C)\otimes I_{m_k}\right),
$$

其中 $s,d_k,m_k\ge1$，$\sum_kd_km_k=D$。这里 $d_k$ 是第 $k$ 个简单矩阵块所作用的 Hilbert 空间维数，$m_k$ 是它在输入空间中的重复次数。

所有存储都必须在实际权重揭示前固定，并逐项满足

$$
\|\Phi(D_j)\|_1=\|D_j\|_1\qquad(j=1,\ldots,m).
$$

区分以下两种资源：

- $d_{\rm all}$：在所有有限维输出 CPTP 通道 $\Phi:\mathcal L(\mathcal H)\to\mathcal L(\mathcal K)$ 中，最小化整个输出空间的维数 $\dim\mathcal K$。若输出包含可读的经典分区标签，它们也计入这个空间。
- $q_{\rm free}$：允许任意有限个免费经典标签，输出为 $M_q(\mathbb C)\otimes\mathbb C^L\cong\bigoplus_{\ell=1}^L M_q(\mathbb C)$，只最小化共享量子寄存器的维数 $q$，$L$ 不计成本。直和上的迹与迹范数均取各块之和。

则两种最小值都达到，并且

$$
\boxed{
 d_{\rm all}=\sum_{k=1}^s d_k,\qquad
 q_{\rm free}=\max_{1\le k\le s}d_k.
}
$$

有限经典存储逐项无损，当且仅当全部 $d_k=1$，也即 $\mathfrak A$ 为交换代数。

证明。首先从范数等号得到输出上的投影表示。取任意逐项无损的有限维输出通道，写出一个有限 Kraus 表示

$$
\Phi(X)=\sum_{a=1}^N K_aXK_a^\dagger,\qquad
\sum_{a=1}^N K_a^\dagger K_a=I.
$$

在输出上取 $F_j$ 为 $\Phi(D_j)$ 的正谱投影。即使输出加权差有零特征值，这仍是一个合法的最优效应。由第 38 节证明中的可逆输入最优效应唯一性，范数等号强制

$$
\Phi^*(F_j)=P_j.
$$

由于 $F_j^2=F_j$，直接展开得

$$
\sum_a(F_jK_a-K_aP_j)^\dagger(F_jK_a-K_aP_j)
=P_j-P_j^2=0.
$$

每项半正定，故

$$
\boxed{F_jK_a=K_aP_j\qquad\text{对全部 }j,a.}
$$

令

$$
\mathcal Q=\operatorname{span}\{\operatorname{ran}K_a:1\le a\le N\}
=\operatorname{supp}\Phi(I)\subseteq\mathcal K.
$$

这里将正算子的支撑视为子空间。交织等式说明每个 $F_j$ 都保持 $\mathcal Q$；自伴性使 $\mathcal Q$ 为约化子空间。因此 $G_j=F_j|_{\mathcal Q}$ 是 $\mathcal Q$ 上的正交投影。

对任何非交换多项式 $p$，逐次使用交织等式可得

$$
p(G_1,\ldots,G_m)K_a
=K_ap(P_1,\ldots,P_m).
$$

若 $p(P_1,\ldots,P_m)=0$，左端就在每个 $K_a$ 的值域上为零，故在它们张成的 $\mathcal Q$ 上为零。反过来，若 $p(G_1,\ldots,G_m)=0$，则所有 $K_ap(P_1,\ldots,P_m)=0$；再用 $\sum_aK_a^\dagger K_a=I$，得到

$$
p(P_1,\ldots,P_m)
=\sum_aK_a^\dagger K_ap(P_1,\ldots,P_m)=0.
$$

输入、输出投影因而满足完全相同的多项式关系。有限维中，含单位的 $*$ 代数生成已经闭合，无需再加入极限。于是

$$
\pi_\Phi:\mathfrak A\longrightarrow\mathcal L(\mathcal Q),
\qquad \pi_\Phi(P_j)=G_j
$$

定义了一个忠实的含单位 $*$ 表示。这里“忠实”指 $\pi_\Phi$ 单射。

在每个简单块 $M_{d_k}(\mathbb C)$ 中选择标准矩阵单位 $e_{ab}^{(k)}$。全部 $e_{aa}^{(k)}$ 是非零、两两正交的投影，且总和为代数单位。忠实表示把它们送到 $\mathcal Q$ 上同样非零且两两正交的投影。它们共有 $\sum_kd_k$ 个，故

$$
\dim\mathcal K\ge\dim\mathcal Q\ge\sum_{k=1}^s d_k.
$$

这给出完整输出的下界。

接着构造达到通道。令 $U$ 实现陈述中的输入分块，对输入矩阵 $X$，将 $UXU^\dagger$ 的第 $k$ 个对角块记为 $X_{kk}$。在输出空间

$$
\mathcal K_0=\bigoplus_{k=1}^s\mathbb C^{d_k}
$$

上定义

$$
\mathcal C_0(X)
=\bigoplus_{k=1}^s\operatorname{tr}_{\mathbb C^{m_k}}(X_{kk}).
$$

该通道先取中央分块，再对重复因子取偏迹。每一步完全正，且输出各块的迹之和为 $\sum_k\operatorname{tr}X_{kk}=\operatorname{tr}X$，所以它是 CPTP 映射。

由于每个 $P_j\in\mathfrak A$，可写

$$
UP_jU^\dagger=\bigoplus_{k=1}^s(P_{j,k}\otimes I_{m_k}),
\qquad P_{j,k}^2=P_{j,k}=P_{j,k}^\dagger.
$$

取输出投影 $\widehat P_j=\bigoplus_kP_{j,k}$，便有 $\mathcal C_0^*(\widehat P_j)=P_j$。因此

$$
\begin{aligned}
\|\mathcal C_0(D_j)\|_1
&\ge2\operatorname{tr}(\widehat P_j\mathcal C_0(D_j))
-\operatorname{tr}\mathcal C_0(D_j)\\
&=2\operatorname{tr}(P_jD_j)-\operatorname{tr}D_j
=\|D_j\|_1.
\end{aligned}
$$

迹范数收缩性给出反向不等式，故所有项都无损。这里不要求 $D_j$ 本身属于 $\mathfrak A$；所保留的正谱投影已足以实现该项判别最优值。通道的输出维数为 $\sum_kd_k$，从而达到 $d_{\rm all}$。

现在计算免费经典标签下的量子寄存器维数。对任意输出于 $\bigoplus_{\ell=1}^L M_q(\mathbb C)$ 的逐项无损通道，上述最优谱投影 $F_j$ 都可取为按经典标签分块的矩阵。于是

$$
\mathcal Q=\bigoplus_{\ell=1}^L\mathcal Q_\ell,
\qquad \dim\mathcal Q_\ell\le q,
\qquad \pi_\Phi=\bigoplus_\ell\pi_\ell.
$$

零支撑的标签可以删去。对第 $k$ 个简单块的中央单位 $z_k=\sum_ae_{aa}^{(k)}$，忠实性保证 $\pi_\Phi(z_k)\ne0$，所以至少有一个标签 $\ell$ 满足 $\pi_\ell(z_k)\ne0$。在该标签内，矩阵单位关系使各 $\pi_\ell(e_{aa}^{(k)})$ 具有相同的秩：$\pi_\ell(e_{ab}^{(k)})$ 给出它们值域间的部分等距。它们的和非零，因而全部非零且两两正交。故

$$
q\ge\dim\mathcal Q_\ell\ge d_k.
$$

对每个 $k$ 应用这个论证，得到 $q\ge\max_kd_k$。这里不同简单块可以在不同的经典标签中出现，因此这个口径给出最大块维数。

为达到该下界，取 $q=\max_kd_k$，并选取等距嵌入 $W_k:\mathbb C^{d_k}\to\mathbb C^q$。用 $s$ 个经典标签定义

$$
\mathcal C_{\rm flag}(X)
=\bigoplus_{k=1}^s
W_k\operatorname{tr}_{\mathbb C^{m_k}}(X_{kk})W_k^\dagger
\in\bigoplus_{k=1}^s M_q(\mathbb C).
$$

此映射 CPTP；第 $k$ 个标签下只使用 $\operatorname{ran}W_k$。输出投影 $\bigoplus_kW_kP_{j,k}W_k^\dagger$ 仍拉回 $P_j$，所以同样逐项保范数。由此 $q_{\rm free}=\max_kd_k$，并且有限个标签已经足够。

纯经典输出就是 $q=1$ 的情形，因此它可行当且仅当全部 $d_k=1$。在交换情形，简单块对应第 38 节的非零联合符号子空间，$s=N$，故完整输出维数仍为 $N$；若经典标签免费，量子寄存器维数为一。在第 39 节的非对易量子比特情形，两个正谱投影生成 $M_2(\mathbb C)$，两种维数都为二，完整量子比特的可恢复性由该节的 Kraus 条件给出。

交织关系还说明，对全部 $X\in\mathfrak A$ 都有

$$
[K_a^\dagger K_b,X]=0.
$$

这是标准算子代数纠错条件在整个输入空间上的形式，见 Bény、Kempf 与 Kribs，*Quantum Error Correction of Observables*，[Theorem 9 及其证明](https://arxiv.org/html/0705.1574)；较早的陈述见同作者 *Generalization of Quantum Error Correction via the Heisenberg Picture*，[Theorem 2，式 (5)](https://arxiv.org/html/quant-ph/0608071)。

免费经典记录下的最大块维数公式已有直接先例：Ballester、Wehner 与 Winter，*State Discrimination with Post-Measurement Information*，[第 5 节、Lemma 5.1 与式 (8)–(11)](https://arxiv.org/html/quant-ph/0608014)。该文研究先受量子存储限制、后获子系综标签时的完美判别，并以支持投影生成代数的最大简单块维数给出精确量子存储门槛。其原文的 $2^q$ 是存储空间维数，对应本节按维数计数的资源。

与本节的对应可逐项写出。对正负部分均非零的 $D_j$，记 $D_j=D_{j,+}-D_{j,-}$，令

$$
t_{j,\pm}=\operatorname{tr}D_{j,\pm}>0,\qquad
\rho_{\pm|j}=\frac{D_{j,\pm}}{t_{j,\pm}},\qquad
p_{\pm|j}=\frac{t_{j,\pm}}{t_{j,+}+t_{j,-}}.
$$

这给出两个正交态组成的二元子系综；各标签 $j$ 可取任意严格正先验。固定通道 $\Phi$ 后，揭示 $j$ 的条件最优成功概率为

$$
p_{\rm succ}(j|\Phi)
=\frac12\left(1+\frac{\|\Phi(D_j)\|_1}{\|D_j\|_1}\right).
$$

所以 $\|\Phi(D_j)\|_1=\|D_j\|_1$ 恰好等价于该子系综的完美判别。可逆性使两态的支持投影正好是 $P_j$ 和 $I-P_j$，因而它们生成的含单位代数就是 $\mathfrak A$。定号的 $D_j$ 在任意 CPTP 通道下都保范数，且只加入 $0$ 或 $I$，可以略去；若全部定号，则 $\mathfrak A=\mathbb C I$、$q_{\rm free}=1$。因此这里的 $q_{\rm free}=\max_kd_k$ 是上述既有判据在加权差任务上的应用。把全部经典分区也计入的 $d_{\rm all}=\sum_kd_k$ 则由本节前面的完整输出下界与达到构造证明。

精确测量压缩及去除重复块的构造另见 Bluhm、Rauber 与 Wolf，*Quantum Compression Relative to a Set of Measurements*，[Definition 4.1、Proposition 6.4 与 Theorem 7.1](https://arxiv.org/html/1708.04898)。该文允许免费经典侧信息，其压缩维数对应这里的 $q$；Theorem 7.1 给出最大矩阵块维数的上界。对于一般非投影效应，不能直接使用这里的 $0/1$ 刚性或宣称生成代数就决定精确压缩维数；该文的一般问题保留了这一区别。输入加权差的可逆性、输出的有限维性以及两种资源的计数口径均属于本定理条件。证毕。

**命题 41.2（五维输入的三维输出与二维量子寄存器）。** 令

$$
\mathcal H=(\mathbb C^2\otimes\mathbb C^2)\oplus\mathbb C,
\qquad P_0=|0\rangle\langle0|,
\qquad P_+=|+\rangle\langle+|,
\qquad |+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},
$$

并取密度矩阵

$$
A=\left(\frac34P_0\otimes\frac{I_2}{2}\right)\oplus\frac14,
\qquad
J=\left(\frac12P_+\otimes\frac{I_2}{2}\right)\oplus\frac12,
$$

以及权重 $c_1=1/2$、$c_2=1$。两个加权差均可逆，正谱投影生成的代数为

$$
\mathfrak A=(M_2(\mathbb C)\otimes I_2)\oplus\mathbb C.
$$

因此

$$
\boxed{d_{\rm all}=3,\qquad q_{\rm free}=2.}
$$

两项量子范数分别为

$$
\|D_{1/2}\|_1=1,\qquad
\|D_1\|_1=\frac{\sqrt{13}+1}{4}.
$$

达到完整输出维数三的通道可以丢弃第二个量子比特的状态，因而无需恢复全部五维输入状态。

证明。$A,J$ 均半正定，且迹分别为 $3/4+1/4=1$、$1/2+1/2=1$。直接分块可得

$$
D_t=E_t\otimes\frac{I_2}{2}\ \oplus\left(\frac t4-\frac12\right),
\qquad
E_t=\begin{pmatrix}
3t/4-1/4&-1/4\\
-1/4&-1/4
\end{pmatrix}.
$$

由于 $\det E_t=-3t/16<0$，$E_t$ 有一正一负两个特征值。在 $t=1/2,1$ 时，末尾标量也严格为负，所以两项 $D_t$ 均可逆。$E_t$ 的迹为 $(3t-2)/4$，因而

$$
\|E_t\|_1=\frac{\sqrt{9t^2+4}}4,
\qquad
\|D_t\|_1=\frac{\sqrt{9t^2+4}+2-t}{4}
\quad(t=1/2,1).
$$

这里使用了 $\|I_2/2\|_1=1$。代入两个权重即得到所列范数。

记 $P_t^{(2)}$ 为 $E_t$ 的正谱投影，则

$$
P_t=P_t^{(2)}\otimes I_2\oplus0.
$$

两个二阶投影具体为

$$
P_{1/2}^{(2)}=\frac15\begin{pmatrix}4&-2\\-2&1\end{pmatrix},
\qquad
P_1^{(2)}=\frac12\left[
I_2+\frac1{\sqrt{13}}\begin{pmatrix}3&-2\\-2&-3\end{pmatrix}
\right].
$$

直接相乘有

$$
[P_{1/2}^{(2)},P_1^{(2)}]
=\frac3{5\sqrt{13}}\begin{pmatrix}0&1\\-1&0\end{pmatrix},
\qquad
[P_{1/2},P_1]^2=-\frac9{325}(I_4\oplus0).
$$

因此中央投影 $I_4\oplus0$ 及其补投影都属于 $\mathfrak A$。两个二阶投影不对易，故生成 $M_2(\mathbb C)$：在其中一个投影的本征基内，另一个投影有非零非对角元，用左右谱投影夹取便得到两个非对角矩阵单位，再加上两个对角投影即可。这说明四维中央块上的生成代数是 $M_2(\mathbb C)\otimes I_2$，末尾中央块是 $\mathbb C$；反向包含关系由两个生成元的分块形式直接成立。故所列代数精确，定理 41.1 给出 $3$ 与 $2$ 两种资源值。

具体的三维达到通道为

$$
\mathcal C_0(X)=\operatorname{tr}_2(X_{11})\oplus X_{22},
$$

其中 $X_{11}$ 是输入的四维对角块，$X_{22}$ 是末尾标量块。它将重复因子取偏迹，并保留中央分区标签。对两个不同纯输入

$$
\rho_r=(P_0\otimes|r\rangle\langle r|)\oplus0,
\qquad r=0,1,
$$

有

$$
\mathcal C_0(\rho_0)=\mathcal C_0(\rho_1)=P_0\oplus0.
$$

所以这个达到压缩没有恢复全部五维输入的左逆。它精确保留的是所列判别任务要求的谱投影代数；第二个量子比特的区别不属于这些观测量。若经典标签免费，同一个中央分块构造使用一个二维量子寄存器及两个经典标签即可，符合 $q_{\rm free}=2$。证毕。

<a id="entry-123"></a>

## 追加锚（新终端）

<a id="section-42"></a>

## 42. 有限量子存储下的最优值达到与严格资源差距

**定理 42.1（免费经典标签的有限达到界）。** 设输入空间为 $\mathbb C^D$，$D\ge1$，$A,J$ 为该空间上的密度矩阵。给定有限正权重表

$$
m\ge1,\qquad 0<c_1<\cdots<c_m,
\qquad D_j=c_jA-J,
$$

以及一个整数 $1\le q\le D$。存储阶段可以使用任意有限个免费经典标签，每个标签携带一个至多 $q$ 维的量子系统；不足 $q$ 维的分支可以补零嵌入 $\mathbb C^q$。通道预先固定，不能依赖后来揭示的实际权重。

具体地，允许任意有限 $n\ge1$ 及完全正映射

$$
\Phi_\ell:\mathbb C^{D\times D}\longrightarrow
\mathbb C^{q\times q},\qquad 1\le\ell\le n,
$$

满足

$$
\sum_{\ell=1}^n\operatorname{tr}\Phi_\ell(X)
=\operatorname{tr}X,
$$

于是总体 CPTP 存储为

$$
\Phi(X)=\bigoplus_{\ell=1}^n\Phi_\ell(X).
$$

各分支保留其未归一化输出，所有标签均计入最终分数，不允许后选择。定义

$$
V_q=\sup_{\substack{n<\infty\\\Phi\ \mathrm{as\ above}}}
\sum_{j=1}^m\|\Phi(D_j)\|_1
=\sup_{\substack{n<\infty\\\Phi\ \mathrm{as\ above}}}
\sum_{\ell=1}^n\sum_{j=1}^m
\|\Phi_\ell(D_j)\|_1.
$$

则这个上确界由至多 $D^2$ 个非零经典分支达到，并有有限变分公式

$$
\boxed{
V_q=
\max_{\substack{E_1,\ldots,E_{D^2}\ge0\\
\operatorname{rank}E_\ell\le q\ (1\le\ell\le D^2)\\
\sum_{\ell=1}^{D^2}E_\ell=I_D}}
\sum_{\ell=1}^{D^2}\sum_{j=1}^m
\bigl\|\sqrt{E_\ell}\,D_j\sqrt{E_\ell}\bigr\|_1.
}
$$

这里允许零效应。公式中的平方根取正平方根，优化变量均为输入空间上的效应；输出量子维数仍是 $q$，并未扩大到 $D$。

进一步，若所有 $D_j$ 均可逆，令

$$
P_j=\mathbf1_{(0,\infty)}(D_j),\qquad
\mathfrak A=C^*(I_D,P_1,\ldots,P_m)
\cong\bigoplus_{k=1}^s
\left(M_{d_k}(\mathbb C)\otimes I_{r_k}\right),
\qquad q_*=\max_k d_k,
$$

其中 $r_k\ge1$ 为输入表示的重数。则

$$
\boxed{
V_q=\sum_{j=1}^m\|D_j\|_1
\quad\Longleftrightarrow\quad q\ge q_*.
}
$$

因此，对每个固定的候选对、权重表与整数 $q<q_*$，存在严格正的最优总损失

$$
\Delta_q:=\sum_{j=1}^m\|D_j\|_1-V_q>0.
$$

增加有限经典标签数不能使这个损失趋于零。

证明。先把每个分支的完全正映射写成有限 Kraus 和

$$
\Phi_\ell(X)=\sum_a K_{\ell a}XK_{\ell a}^\dagger,
\qquad K_{\ell a}:\mathbb C^D\longrightarrow\mathbb C^q,
\qquad
\sum_{\ell,a}K_{\ell a}^\dagger K_{\ell a}=I_D.
$$

改用新的存储仪器，将 $(\ell,a)$ 作为经典标签，每个分支只使用一个 Kraus 算子：

$$
\widetilde\Phi(X)
=\bigoplus_{\ell,a}K_{\ell a}XK_{\ell a}^\dagger.
$$

这是优化域内另一个合法 CPTP 通道。对每个 $j$，三角不等式给出

$$
\sum_\ell\|\Phi_\ell(D_j)\|_1
\le\sum_{\ell,a}\|K_{\ell a}D_jK_{\ell a}^\dagger\|_1.
$$

故这个替换不降低目标值。它使用的是优化时重新选择仪器的自由；没有假定一个已经实现且丢弃环境的通道，还能事后取回其 Kraus 标签。全部新增标签仍保留在输出中，没有删去不利分支。

对一个这样的算子 $K$，置

$$
E=K^\dagger K\ge0,\qquad \operatorname{rank}E\le q.
$$

极分解 $K=U\sqrt E$ 中，$U$ 在 $\operatorname{supp}E$ 上为等距映射。矩阵 $\sqrt E D_j\sqrt E$ 的支撑包含于该子空间，因此等距嵌入只增添零特征值，并有

$$
\|KD_jK^\dagger\|_1
=\|U\sqrt E D_j\sqrt E U^\dagger\|_1
=\|\sqrt E D_j\sqrt E\|_1.
$$

反过来，对任意有限效应表

$$
E_\ell\ge0,\qquad \operatorname{rank}E_\ell\le q,
\qquad \sum_\ell E_\ell=I_D,
$$

为每个非零效应选择等距映射

$$
U_\ell:\operatorname{supp}E_\ell\longrightarrow\mathbb C^q,
\qquad K_\ell=U_\ell\sqrt{E_\ell}.
$$

把 $U_\ell$ 在支撑外延拓为零，并对零效应取 $K_\ell=0$。于是 $K_\ell^\dagger K_\ell=E_\ell$，通道

$$
\Phi_E(X)=\bigoplus_\ell K_\ell X K_\ell^\dagger
$$

为 CPTP，且逐项达到效应表的范数目标。故原上确界精确等于所有有限秩受限效应表上

$$
\sum_\ell f(E_\ell),\qquad
f(E)=\sum_{j=1}^m\|\sqrt E D_j\sqrt E\|_1
$$

的上确界。

现在证明效应数可以统一限制为 $D^2$。函数 $f$ 在正半定矩阵上连续，且对每个 $t\ge0$ 有

$$
f(tE)=t f(E).
$$

从任意有限可行效应表出发，先删去零效应。若非零效应数大于 $D^2$，由于 $D$ 阶 Hermitian 矩阵构成 $D^2$ 维实向量空间，存在不全为零的实数 $a_\ell$，满足

$$
\sum_\ell a_\ell E_\ell=0.
$$

每个非零效应的迹严格为正。对该等式取迹可知，$a_\ell$ 必须同时含有正数和负数。把整组系数变号也保持该关系，故可以选择方向使

$$
b:=\sum_\ell a_\ell f(E_\ell)\ge0.
$$

沿该方向取

$$
t_*:=\min_{\ell:\,a_\ell<0}\frac{-1}{a_\ell}>0,
\qquad
E'_\ell=(1+t_*a_\ell)E_\ell.
$$

所有缩放系数非负，至少一个原非零效应变为零。正性、秩上界以及总和为 $I_D$ 的条件均保持；齐次性给出

$$
\sum_\ell f(E'_\ell)
=\sum_\ell f(E_\ell)+t_*b
\ge\sum_\ell f(E_\ell).
$$

每次至少删去一个非零效应，有限次重复后得到至多 $D^2$ 个效应，且目标不降。这一消去从任意有限方案开始，不预先假设上确界已经达到。

把效应表补零至 $D^2$ 项。所列固定槽位可行集非空：选一个输入正交基的 $D$ 个秩一投影，再补零即可，因为 $q\ge1$。每个效应自动满足 $0\le E_\ell\le I_D$。正性、总和以及 $\operatorname{rank}E_\ell\le q$ 都是闭条件，后者可由所有 $(q+1)$ 阶子式为零表述。因此可行集在有限维实向量空间中闭且有界，故紧。正矩阵平方根与迹范数连续，所以目标达到最大值。结合前面的消去与物理实现，得到有限变分公式和至多 $D^2$ 个非零经典分支的达到结论。秩约束通常不凸；这个紧集公式不自动给出一般闭式或半正定规划。

最后假设全部 $D_j$ 可逆。任意 CPTP 通道逐项满足

$$
\|\Phi(D_j)\|_1\le\|D_j\|_1.
$$

若 $q\ge q_*$，第 41 节的中心分支与重数偏迹构造使用免费经典标签和至多 $q_*$ 维量子分支，同时保留全部范数。将其分支嵌入 $\mathbb C^q$，得到 $V_q=\sum_j\|D_j\|_1$。

若 $q<q_*$ 而两者相等，前面已经证明最大值由一个有限分支通道达到。各项损失均非负而总和为零，故这个通道对每项都有

$$
\|\Phi(D_j)\|_1=\|D_j\|_1.
$$

这与第 41 节的必要条件 $q\ge\max_k d_k$ 矛盾。因此 $\Delta_q>0$。严格差距来自达到性和精确无损障碍共同作用；只知道没有无损通道，还不足以排除一列损失趋于零的通道。

上面的有限达到证明本身不要求任何 $D_j$ 可逆，也适用于任意固定有限组 Hermitian 输入差。可逆性只用于最后调用第 41 节的符号投影代数判据。这里没有给出跨候选对或权重表统一的正损失常数，也没有从小损失推出一般恢复误差界。

所用标量依赖扰动与 D'Ariano、Lo Presti、Perinotti，*Classical randomness in quantum measurements*，[推论 7 及其证明](https://arxiv.org/abs/quant-ph/0408115) 中的标准 POVM 方法一致；本节利用目标的正齐次性选择不降方向，同时保持各效应的秩上界。Bluhm、Rauber、Wolf，*Quantum compression relative to a set of measurements*，[引理 5.2、引理 5.3 与定理 5.1](https://arxiv.org/abs/1708.04898) 也通过限制经典辅助规模与紧性证明压缩维数的稳定性，但其 $D^4$ 标签界用于在保持给定复合通道不变的条件下重构压缩与解压缩映射。本节只优化所列有限范数总分，允许更换存储仪器并在权重揭示后分别选择最终判别；$D^2$ 界不承担保持原复合通道或共同解压缩映射的要求。证毕。

<a id="entry-125"></a>

## 追加锚（新终端）

<a id="section-43"></a>

## 43. 奇异加权差的交叉支撑判据与经典无损存储

**定理 43.1（有序权重的正负支撑判据）。** 设 $A,J$ 为 $\mathbb C^D$ 上的密度矩阵，$D\ge1$，预先给定有限权重表

$$
m\ge1,\qquad 0<c_1<\cdots<c_m,\qquad D_j=c_jA-J.
$$

允许 $D_j$ 奇异、定号或为零。分别记正谱、负谱及零谱投影为

$$
P_j^+=\mathbf1_{(0,\infty)}(D_j),\qquad
P_j^-=\mathbf1_{(-\infty,0)}(D_j),\qquad
Z_j=I_D-P_j^+-P_j^-.
$$

存在一个有限经典输出 CPTP 通道，在实际权重揭示前固定，并满足

$$
\|\Phi(D_j)\|_1=\|D_j\|_1
\qquad(1\le j\le m),
$$

当且仅当

$$
\boxed{
P_i^+P_j^-=0\qquad\text{对全部 }1\le i<j\le m.
}
$$

条件成立时，令

$$
\mathcal S_j=\operatorname{span}
\{\operatorname{ran}P_i^+:1\le i\le j\},
\qquad Q_j=\operatorname{proj}_{\mathcal S_j},
\qquad Q_0=0,\quad Q_{m+1}=I_D.
$$

这些投影满足

$$
Q_0\le Q_1\le\cdots\le Q_m\le Q_{m+1},
\qquad P_j^+\le Q_j\le I_D-P_j^-.
$$

因此

$$
M_k=Q_{k+1}-Q_k,\qquad 0\le k\le m,
$$

是一组共同投影测量；删去零效应后，至多 $\min\{D,m+1\}$ 个经典标签足以同时无损。这里给出的是达到该任务的标签上界，没有断言每个输入都需要这么多标签。

证明。先确定奇异加权差的全部最优效应。对任意 Hermitian 矩阵 $H$，写其 Jordan 分解为

$$
H=H_+-H_-,\qquad H_+,H_-\ge0,\qquad H_+H_-=0.
$$

令 $P^+,P^-,Z$ 为相应的正、负、零谱投影。对效应 $0\le F\le I_D$，有

$$
\operatorname{tr}H_+-\operatorname{tr}(FH)
=\operatorname{tr}((I_D-F)H_+)+\operatorname{tr}(FH_-)
\ge0.
$$

两项均非负。正矩阵乘积的迹为零，等价于它们的正平方根乘积为零。因此等号成立，当且仅当 $F$ 在 $\operatorname{ran}P^+$ 上为恒等、在 $\operatorname{ran}P^-$ 上为零。由于 $F$ 自伴，这两个子空间与其正交补之间的非对角块也为零；于是全部最优效应精确写成

$$
\boxed{
F=P^++R,\qquad 0\le R\le Z,
}
$$

等价地，$P^+\le F\le I_D-P^-$。它们都满足二元判别的变分等式

$$
2\operatorname{tr}(FH)-\operatorname{tr}H=\|H\|_1.
$$

这里 $0\le R\le Z$ 已保证 $R$ 支撑在零特征子空间。若 $H$ 可逆，该自由消失，最优效应唯一；若 $H=0$，整个效应区间都最优。

对加权密度矩阵差，这个完整最优效应区间是量子 Neyman–Pearson 引理的标准形式，见 Jenčová，*Reversibility conditions for quantum operations*，[引理 7](https://arxiv.org/abs/1107.0453)。在该引理中取 $\sigma=A$、$\rho=J$、$t=1/c_j$，则 $\sigma-t\rho=D_j/c_j$；因为 $c_j>0$，正、负、零谱子空间以及最优效应集合均不改变。

现设存在逐项无损的有限经典存储。它由某个有限 POVM $(E_\ell)_\ell$ 给出，输出第 $\ell$ 个标签的概率为 $\operatorname{tr}(E_\ell\rho)$。定义

$$
a_\ell=\operatorname{tr}(E_\ell A)\ge0,\qquad
b_\ell=\operatorname{tr}(E_\ell J)\ge0,
$$

以及输入效应

$$
F_j=\sum_{\ell:\,c_ja_\ell-b_\ell>0}E_\ell.
$$

由经典范数的逐标签绝对值表达，

$$
2\operatorname{tr}(F_jD_j)-\operatorname{tr}D_j
=\sum_\ell|c_ja_\ell-b_\ell|
=\|\Phi(D_j)\|_1
=\|D_j\|_1.
$$

因此每个 $F_j$ 都是对应加权差的最优效应。因为 $a_\ell\ge0$，每个 $c_ja_\ell-b_\ell$ 随 $j$ 不减，正号标签集合随之嵌套，所以

$$
F_i\le F_j\qquad(i<j).
$$

定义直接使用严格正号，不需要除以 $a_\ell$。当 $a_\ell=0$ 时，由 $b_\ell\ge0$，该标签永不入选；读数恰为零时也排除，不影响上述等式与嵌套性。

固定 $i<j$。最优效应条件给出

$$
P_i^+\le F_i\le F_j\le I_D-P_j^-.
$$

对任意 $v\in\operatorname{ran}P_j^-$，夹取此不等式得到 $\langle v,P_i^+v\rangle=0$，故 $P_i^+v=0$。于是 $P_i^+P_j^-=0$，证明必要性。这里没有将一般 $F_j$ 假定为投影，也没有从两效应的共同来源直接断言它们对易。

反过来，设所有交叉支撑条件成立。对 $i\le j$，$\operatorname{ran}P_i^+$ 与 $\operatorname{ran}P_j^-$ 正交；$i=j$ 的情形由谱分解自动成立。因此陈述中的 $\mathcal S_j$ 包含 $\operatorname{ran}P_j^+$，并且与 $\operatorname{ran}P_j^-$ 正交，给出

$$
P_j^+\le Q_j\le I_D-P_j^-.
$$

子空间 $\mathcal S_j$ 递增，所以 $Q_j$ 是嵌套的最优投影扩展。相邻投影差 $M_k=Q_{k+1}-Q_k$ 均为正交投影，彼此正交，且总和为 $I_D$。用这组 PVM 作经典存储，并在权重 $c_j$ 揭示后把 $k<j$ 的标签归为第一种判别结果，则其输入效应为

$$
\sum_{k=0}^{j-1}M_k=Q_j.
$$

这个效应达到 $D_j$ 的二元最优值。存储后范数至少为该决策给出的 $\|D_j\|_1$，迹范数收缩性又给出反向不等式，因而逐项无损。投影总数为 $m+1$，非零项又是两两正交的非零子空间投影，所以非零数不超过 $D$。全部标签均保留，没有后选择。

一般有限组判别问题的正确条件，是能够从各自的最优效应集合中选出彼此兼容的二元测量；兼容指它们都是某一共同 POVM 的经典后处理。对任意 Hermitian 差，上述计算把每个最优集合具体写成 $P_j^++[0,Z_j]$。兼容的一组选取产生共同经典存储，反向则由存储后的最优决策得到这样的选取。最优效应不唯一时，只需存在一组兼容选取；这一一般原则见 Carmeli、Heinosaari、Toigo，*State discrimination with post-measurement information and incompatibility of quantum measurements*，[定理 1 及其后的说明](https://arxiv.org/html/1804.09693)。对本节的 $D_j=c_jA-J$，第 37 节的系综归一化同样适用。

本节在同一候选对与递增正权重的条件下，利用逐标签读数的单调性，把兼容性进一步化为所列交叉支撑判据，并明确构造嵌套的投影扩展。若所有 $D_j$ 可逆，则 $I_D-P_j^-=P_j^+$，交叉条件退化为 $P_i^+\le P_j^+$，与第 38 节在有序权重下得到的嵌套判据一致。奇异情形保留了零特征子空间的选择自由，不能直接要求原始正谱投影彼此对易。证毕。

**命题 43.2（严格正定候选的奇异不定反例）。** 在 $\mathbb C^3$ 的标准基 $e_1,e_2,e_3$ 下取

$$
A=\frac18\begin{pmatrix}
2&3&0\\3&5&0\\0&0&1
\end{pmatrix},\qquad
J=\frac1{27}\begin{pmatrix}
5&9&0\\9&17&0\\0&0&5
\end{pmatrix},
\qquad c=\frac89,\quad d=\frac{32}{27}.
$$

这两个候选都是严格正定密度矩阵，$c<d$。令 $D_t=tA-J$，则

$$
D_c=\frac1{27}\begin{pmatrix}
1&0&0\\0&-2&0\\0&0&-2
\end{pmatrix},\qquad
D_d=\frac1{27}\begin{pmatrix}
3&3&0\\3&3&0\\0&0&-1
\end{pmatrix}.
$$

两个差都不定，$D_c$ 可逆而 $D_d$ 奇异。它们的正谱投影不对易，但标准三结果 PVM 同时保留

$$
\|D_c\|_1=\frac5{27},\qquad
\|D_d\|_1=\frac7{27}.
$$

对这两个任务，最少经典标签数和最小完整量子输出维数均为三；若经典标签免费，所需量子寄存器维数为一。

证明。$A,J$ 的迹均为一。它们的顺序主子式分别为

$$
\left(\frac14,\frac1{64},\frac1{512}\right),\qquad
\left(\frac5{27},\frac4{729},\frac{20}{19683}\right),
$$

全部严格为正，故二者严格正定。代入两个权重得到陈述中的加权差。$D_c$ 的特征值为 $1/27,-2/27,-2/27$；$D_d$ 的特征值为 $6/27,0,-1/27$，因此二者均含有严格正、负特征值，范数也是所列值。

令

$$
u=\frac{e_1+e_2}{\sqrt2},\qquad
w=\frac{e_1-e_2}{\sqrt2}.
$$

相应投影为

$$
P_c^+=|e_1\rangle\langle e_1|,\qquad
P_d^+=|u\rangle\langle u|,\qquad
P_d^-=|e_3\rangle\langle e_3|,\qquad
Z_d=|w\rangle\langle w|.
$$

直接计算得

$$
[P_c^+,P_d^+]
=\frac12\begin{pmatrix}0&1&0\\-1&0&0\\0&0&0\end{pmatrix}\ne0.
$$

但 $P_c^+P_d^-=0$，所以满足定理 43.1 的交叉支撑条件。其嵌套最优投影是

$$
Q_c=|e_1\rangle\langle e_1|,\qquad
Q_d=|e_1\rangle\langle e_1|+|e_2\rangle\langle e_2|
=P_d^++Z_d.
$$

对应 PVM 恰为三个标准基投影。测量两个差得到的未归一化对角读数分别为

$$
\frac1{27}(1,-2,-2),\qquad
\frac1{27}(3,3,-1).
$$

绝对值之和分别为 $5/27$ 与 $7/27$，直接验证共同经典测量无损。

现在证明整个输出至少需要三维。设任意有限维 CPTP 通道 $\Phi(X)=\sum_a K_aXK_a^\dagger$ 对这两项无损，并令

$$
\mathcal R_r=\operatorname{span}_a\{K_ae_r\},
\qquad r=1,2,3.
$$

由迹保持，$\sum_a\|K_ae_r\|^2=1$，所以每个 $\mathcal R_r$ 都非零。对正矩阵 $B,C$，$\|B-C\|_1=\operatorname{tr}B+\operatorname{tr}C$ 当且仅当其支撑正交：取 $B-C$ 的最优正谱投影 $F$，等号要求 $\operatorname{tr}((I-F)B)=\operatorname{tr}(FC)=0$，分别将两个支撑置于 $F$ 的值域与核中；反向由正交分块成立。

将这一条件用于 $D_c$ 的正负部分，无损性给出

$$
\mathcal R_1\perp\mathcal R_2,\qquad
\mathcal R_1\perp\mathcal R_3.
$$

再用于 $D_d=(6|u\rangle\langle u|-|e_3\rangle\langle e_3|)/27$，得到对所有 $a,b$ 都有

$$
\langle K_a(e_1+e_2),K_be_3\rangle=0.
$$

其中 $\langle K_ae_1,K_be_3\rangle=0$ 已由第一项确定，相减可得 $\langle K_ae_2,K_be_3\rangle=0$。所以三个非零子空间 $\mathcal R_1,\mathcal R_2,\mathcal R_3$ 两两正交，整个输出空间至少三维。标准三标签通道达到该下界，也证明两个经典标签不够。免费标签的口径下，同一实现为纯经典输出，故最小量子寄存器维数为一。

最后核对第 41 节公式的适用边界。此例的标准正谱投影生成

$$
C^*(I_3,P_c^+,P_d^+)=M_2(\mathbb C)\oplus\mathbb C.
$$

事实上，上面对易子的平方为 $-(I_2\oplus0)/4$，故两个中央分区投影都在生成代数中；在前二维内，两个不对易秩一投影生成全部 $M_2(\mathbb C)$，末尾为标量块。因此若删去第 41 节的可逆性前提而直接使用其最大块公式，会给出量子寄存器维数二，与这里已达到且最小的维数一矛盾。其完整输出公式在此恰好仍给出三，不能据这个例子声称该数值也失效。

此例的经典无损并不来自某一项半正定而自动保范数：两项都不定，保留它们的最优判别仍需要三个输出维数。改变判据的是 $D_d$ 的零特征子空间；把它加入正谱投影后，最优效应成为能与第一项共同读取的 $Q_d$。证毕。

<a id="entry-127"></a>

## 追加锚（新终端）

<a id="section-44"></a>

## 44. 交叉支撑的定量损失界

**定理 44.1（有序权重的显式经典损失下界）。** 沿用第 43 节的有限维任务：$A,J$ 为 $\mathbb C^D$ 上的密度矩阵，$D\ge1$，且

$$
m\ge2,\qquad 0<c_1<\cdots<c_m,\qquad D_k=c_kA-J.
$$

允许这些加权差奇异。固定 $i<j$，假设相关的正、负谱投影

$$
P=P_i^+=\mathbf1_{(0,\infty)}(D_i)\ne0,\qquad
Q=P_j^-=\mathbf1_{(-\infty,0)}(D_j)\ne0.
$$

在这两个非零支撑上定义严格正的谱间隙

$$
\alpha=\min\{\lambda>0:\lambda\in\operatorname{spec}D_i\},
\qquad
\beta=\min\{-\lambda:\lambda<0,\ \lambda\in\operatorname{spec}D_j\}.
$$

令 $r_P=\operatorname{rank}P$、$r_Q=\operatorname{rank}Q$，并记

$$
\boxed{
\mathsf B_{ij}=\alpha r_P+\beta r_Q-\|\alpha P-\beta Q\|_1.
}
$$

对任意预先固定的有限经典输出 CPTP 通道 $\Phi$，令

$$
\delta_k(\Phi)=\|D_k\|_1-\|\Phi(D_k)\|_1.
$$

则

$$
\boxed{
\delta_i(\Phi)+\delta_j(\Phi)\ge\mathsf B_{ij}\ge0,
\qquad
\mathsf B_{ij}>0\ \Longleftrightarrow\ PQ\ne0.
}
$$

特别地，一对违反第 43 节交叉支撑条件的权重，就给出对所有有限经典存储统一有效的严格正总损失下界。它针对固定的候选对与权重表，不是跨任务的统一常数。

若 $P,Q$ 都为秩一投影，记 $\chi=\operatorname{tr}(PQ)\in[0,1]$，则

$$
\boxed{
\mathsf B_{ij}
=\alpha+\beta-\sqrt{(\alpha+\beta)^2-4\alpha\beta\chi}.
}
$$

若相关支撑之一为零，则不使用上述谱间隙定义；这一对权重的下界可直接记为零。$\mathsf B_{ij}$ 是整体判别损失的下界，未断言它等于最优总损失。

证明。固定经典存储对应的有限 POVM $(E_\ell)_\ell$。对每个权重，选取它在经典输出上的正号决策并拉回输入：

$$
F_k=\sum_{\ell:\,c_k\operatorname{tr}(E_\ell A)-\operatorname{tr}(E_\ell J)>0}E_\ell.
$$

与第 43 节相同，各输出读数随 $c_k$ 不减，所以

$$
0\le F_i\le F_j\le I_D.
$$

这里的 $F_k$ 实现存储后的最优二元决策；不要求它在原输入上已经无损，也不要求它是投影。

写 $D_k=D_{k,+}-D_{k,-}$。利用 $F_k$ 的经典最优性，单项损失有精确表达

$$
\begin{aligned}
\delta_k(\Phi)
&=\|D_k\|_1-2\operatorname{tr}(F_kD_k)+\operatorname{tr}D_k\\
&=2\operatorname{tr}((I_D-F_k)D_{k,+})
+2\operatorname{tr}(F_kD_{k,-}).
\end{aligned}
$$

右端两项都非负。谱间隙定义给出 $D_{i,+}\ge\alpha P$ 和 $D_{j,-}\ge\beta Q$，所以

$$
\delta_i(\Phi)+\delta_j(\Phi)
\ge2\alpha\operatorname{tr}((I_D-F_i)P)
+2\beta\operatorname{tr}(F_jQ).
$$

再由 $F_i\le F_j$ 得到

$$
\begin{aligned}
\delta_i(\Phi)+\delta_j(\Phi)
&\ge2\left[\alpha\operatorname{tr}((I_D-F_i)P)
+\beta\operatorname{tr}(F_iQ)\right]\\
&\ge2\min_{0\le F\le I_D}
\left[\alpha\operatorname{tr}((I_D-F)P)
+\beta\operatorname{tr}(FQ)\right].
\end{aligned}
$$

这个辅助最小值可以精确求出。令 $T=\alpha P-\beta Q$，由正谱投影达到的变分公式，有

$$
\max_{0\le F\le I_D}\operatorname{tr}(FT)
=\operatorname{tr}T_+
=\frac{\|T\|_1+\operatorname{tr}T}{2}.
$$

因而

$$
\begin{aligned}
&2\min_{0\le F\le I_D}
\left[\alpha\operatorname{tr}((I_D-F)P)
+\beta\operatorname{tr}(FQ)\right]\\
&=2\alpha r_P-2\operatorname{tr}T_+
=\alpha r_P+\beta r_Q-\|\alpha P-\beta Q\|_1
=\mathsf B_{ij}.
\end{aligned}
$$

这证明下界。辅助二元优化的精确性不使前面的谱间隙替换、丢去非负项及 $F_i\le F_j$ 的估计自动成为等号。

接着判断何时严格为正。三角不等式给出

$$
\|\alpha P-\beta Q\|_1\le\alpha r_P+\beta r_Q.
$$

第 43 节已证明，对两个正矩阵，差的迹范数等于两迹之和，当且仅当它们的支撑正交。这里 $\alpha,\beta>0$，两个支撑正好是 $\operatorname{ran}P$ 与 $\operatorname{ran}Q$，所以

$$
\mathsf B_{ij}=0\ \Longleftrightarrow\ PQ=0.
$$

如果整组任务中存在 $P_i^+P_j^-\ne0$，这两个投影自动非零，可以使用本定理。其余单项损失也非负，因此整组总损失至少为该对权重的 $\mathsf B_{ij}>0$。这个显式结论直接排除了通过增加有限经典标签数而把总损失逼近零的方案。

最后计算秩一情形。写 $P=|p\rangle\langle p|$、$Q=|q\rangle\langle q|$，其中 $p,q$ 为单位向量，则 $\chi=|\langle p,q\rangle|^2$。若 $\chi<1$，在二维空间 $\operatorname{span}\{p,q\}$ 上，$T$ 的迹与行列式分别为

$$
\operatorname{tr}T=\alpha-\beta,\qquad
\det T=-\alpha\beta(1-\chi)<0.
$$

其两个非零特征值异号，故

$$
\|T\|_1
=\sqrt{(\alpha-\beta)^2+4\alpha\beta(1-\chi)}
=\sqrt{(\alpha+\beta)^2-4\alpha\beta\chi}.
$$

在正交补上只有零特征值。若 $\chi=1$，则 $P=Q$，有 $\|T\|_1=|\alpha-\beta|$，同一个根式仍成立，此时 $\mathsf B_{ij}=2\min\{\alpha,\beta\}$。这给出完整的秩一公式，包括 $\chi=0$ 时下界为零的情形。

上述辅助优化是标准 Helstrom 二元判别公式的直接应用。具体令 $C=\alpha r_P+\beta r_Q$，把 $P/r_P$ 与 $Q/r_Q$ 视为两个密度矩阵，先验分别取 $\alpha r_P/C$ 与 $\beta r_Q/C$；其最小错误概率乘以 $2C$ 就是 $\mathsf B_{ij}$。该公式及正谱投影达到策略见 Ballester、Wehner 与 Winter，*State Discrimination with Post-Measurement Information*，[Theorem 2.1](https://arxiv.org/html/quant-ph/0608014)，其中明确归于 Helstrom。本节把第 43 节的有序决策效应与这个标准二元公式结合；不将辅助公式本身作为新结果。证毕。

**命题 44.2（交叉支撑界与第 40 节下界互不支配）。** 在两者共同适用的量子比特任务中，定理 44.1 的 $\mathsf B_{ij}$ 与定理 40.1 的 $\mathsf L$ 没有普遍的大小顺序。

具体地，取

$$
A=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
J=\frac1{10}\begin{pmatrix}9&3\\3&1\end{pmatrix},
\qquad c=\frac14,\quad d=4,
\qquad \mu=\frac{\sqrt{265}-15}{40}>0.
$$

两候选不对易，两个加权差都严格不定。此时两个下界为

$$
\mathsf B_{cd}=\mu\left(5-\sqrt{\frac{677}{53}}\right),
\qquad
\mathsf L=2\mu\left(5-\sqrt{\frac{1125}{53}}\right),
$$

并且

$$
\boxed{0<\mathsf L<\mu<\mathsf B_{cd}.}
$$

另一方面，在命题 40.2 的混态例中，$\mathsf B_{12}=\mathsf L/2>0$，因此第 40 节的下界严格更强。

证明。这里 $A$ 是秩一投影，$J=vv^\dagger/10$，其中 $v=(3,1)^{\mathsf T}$ 且 $v^\dagger v=10$，所以两者都是纯态密度矩阵。由于 $J$ 的非对角元非零，$[A,J]\ne0$。两个加权差为

$$
D_c=\frac1{20}\begin{pmatrix}-13&-6\\-6&-2\end{pmatrix},
\qquad
D_d=\frac1{10}\begin{pmatrix}31&-3\\-3&-1\end{pmatrix}.
$$

它们的行列式分别为 $-1/40$ 与 $-2/5$，因此都严格不定。迹分别为 $-3/4$ 与 $3$，迹范数分别为

$$
\|D_c\|_1=\frac{\sqrt{265}}{20},\qquad
\|D_d\|_1=\frac{\sqrt{265}}5.
$$

按第 40 节的记号，正、负本征值绝对值中的较小者为 $\mu_c=\mu$、$\mu_d=4\mu$。由于 $c<1<d$，$D_c$ 的正本征值较小、$D_d$ 的负本征值绝对值较小，所以定理 44.1 中的两个谱间隙恰为

$$
\alpha=\mu,\qquad\beta=4\mu.
$$

再令 $S_t=2P_t^+-I_2$。直接去迹并除以相应的 $\|D_t\|_1/2$ 得到

$$
S_c=\frac1{\sqrt{265}}\begin{pmatrix}-11&-12\\-12&11\end{pmatrix},
\qquad
S_d=\frac1{\sqrt{265}}\begin{pmatrix}16&-3\\-3&-16\end{pmatrix}.
$$

因此

$$
\kappa=\frac12\operatorname{tr}(S_cS_d)=-\frac{28}{53},
\qquad \eta=|\kappa|=\frac{28}{53},
\qquad
\chi=\operatorname{tr}(P_c^+P_d^-)=\frac{1-\kappa}{2}=\frac{81}{106}.
$$

代入两个定理，根式中的量分别化为

$$
(\alpha+\beta)^2-4\alpha\beta\chi
=\mu^2\frac{677}{53},
$$

$$
\mu_c^2+\mu_d^2+2\mu_c\mu_d\eta
=\mu^2\frac{1125}{53}.
$$

这给出所列两个下界。它们的严格比较只需要有理数平方比较：

$$
\frac{1125}{53}<25,
\qquad
\frac{1125}{53}>\frac{81}{4},
\qquad
\frac{677}{53}<16.
$$

第一式给出 $\mathsf L>0$；第二式给出 $\mathsf L<2\mu(5-9/2)=\mu$；第三式给出 $\mathsf B_{cd}>\mu(5-4)=\mu$。又因 $265>15^2$，$\mu>0$，所有不等号方向确定。

为得到反向的严格比较，取命题 40.2 的

$$
A=\begin{pmatrix}3/4&0\\0&1/4\end{pmatrix},\qquad
J=\begin{pmatrix}1/2&1/4\\1/4&1/2\end{pmatrix},
\qquad c=1,\quad d=2.
$$

该节已经算得

$$
\mu_c=\frac{\sqrt2}{4},\qquad
\mu_d=\frac{\sqrt5-2}{4},\qquad
\kappa=\eta=\frac3{\sqrt{10}}>0.
$$

此时同样有 $\alpha=\mu_c$、$\beta=\mu_d$。把 $\chi=(1-\kappa)/2$ 代入秩一公式，得到

$$
\mathsf B_{12}
=\mu_c+\mu_d-\sqrt{\mu_c^2+\mu_d^2+2\mu_c\mu_d\kappa}
=\frac{\mathsf L}{2}.
$$

由第 40 节的 $\mathsf L>0$，这是严格较小的下界。两个精确例子共同排除了任一方的普遍数值支配关系。

第 44 节的界适用于任意有限输入维数及奇异加权差，第 40 节则同时给出两项量子比特任务的经典损失上下界。在共同适用处可以取两个下界的较大者；这里保留第 40 节的结论，没有用新界替代它，也未把上述纯态例中的任一下界宣称为实际最优损失。证毕。

<a id="entry-129"></a>

## 追加锚（新终端）

<a id="section-45"></a>

## 45. 最优分数的连续性与精确存储维数的跳变

**定理 45.1（固定存储预算下的迹范数扰动界）。** 固定整数 $D,m\ge1$ 与 $1\le q\le D$。对 $\mathbb C^D$ 上的任意有限 Hermitian 矩阵表

$$
\mathbf H=(H_1,\ldots,H_m),
$$

沿用第 42 节的存储域：通道输出至任意有限个免费经典标签，每个标签携带至多 $q$ 维量子系统，各分支输出不归一化且不作后选择。定义

$$
V_q(\mathbf H)=\sup_\Phi\sum_{j=1}^m\|\Phi(H_j)\|_1,
\qquad
B(\mathbf H)=\sum_{j=1}^m\|H_j\|_1,
\qquad
\Delta_q(\mathbf H)=B(\mathbf H)-V_q(\mathbf H).
$$

这里不同矩阵表上的最优通道可以不同，但允许的通道集合由同一组 $D,m,q$ 固定。对另一组同维同长矩阵表 $\mathbf H'=(H'_1,\ldots,H'_m)$，令

$$
d_1(\mathbf H,\mathbf H')=
\sum_{j=1}^m\|H_j-H'_j\|_1.
$$

则

$$
\boxed{
|V_q(\mathbf H)-V_q(\mathbf H')|
\le d_1(\mathbf H,\mathbf H'),
\qquad
|\Delta_q(\mathbf H)-\Delta_q(\mathbf H')|
\le2d_1(\mathbf H,\mathbf H').
}
$$

不要求任何输入差可逆。若仅改变同一密度矩阵对 $A,J$ 的权重，令 $H_j=c_jA-J$、$H'_j=c'_jA-J$，则距离精确为

$$
d_1(\mathbf H,\mathbf H')=\sum_{j=1}^m|c_j-c'_j|.
$$

定义最小无损量子寄存器维数

$$
q_{\min}(\mathbf H)=
\min\{q\in\{1,\ldots,D\}:\Delta_q(\mathbf H)=0\}.
$$

第 42 节的达到性使 $\Delta_q=0$ 等价于存在有限标签的逐项无损通道。对每个固定 $q$，集合 $\{\mathbf H:q_{\min}(\mathbf H)\le q\}$ 是闭集。因此 $q_{\min}$ 是下半连续的：在任意固定矩阵表处，足够小的扰动不能降低该处的最小无损量子维数，但可以使它升高。

证明。首先，对 Hermitian 矩阵 $X=X_+-X_-$，正性与迹保持给出

$$
\|\Phi(X)\|_1
\le\|\Phi(X_+)\|_1+\|\Phi(X_-)\|_1
=\operatorname{tr}X_++\operatorname{tr}X_-
=\|X\|_1.
$$

所以 $0\le V_q(\mathbf H)\le B(\mathbf H)$。对任一共同允许通道，反三角不等式与上述收缩性给出

$$
\begin{aligned}
\left|\sum_j\|\Phi(H_j)\|_1
-\sum_j\|\Phi(H'_j)\|_1\right|
&\le\sum_j\|\Phi(H_j-H'_j)\|_1\\
&\le d_1(\mathbf H,\mathbf H').
\end{aligned}
$$

该界对整个允许通道集合一致。先取一侧上确界，再交换两组矩阵表，便得到 $V_q$ 的扰动界；这一步不要求两组最优通道相同，也不预先使用最大值达到性。对 $B$ 直接用反三角不等式同样得到

$$
|B(\mathbf H)-B(\mathbf H')|
\le d_1(\mathbf H,\mathbf H').
$$

将两式相加即得 $\Delta_q$ 的系数二界。仅改变权重时，$H_j-H'_j=(c_j-c'_j)A$，而 $A\ge0$、$\operatorname{tr}A=1$，所以 $\|H_j-H'_j\|_1=|c_j-c'_j|$。

预算从 $q$ 增大时，可以把原输出量子系统等距嵌入较大空间，故 $V_q$ 不减而 $\Delta_q$ 不增。恒等存储使用 $q=D$ 即可无损，所以 $q_{\min}$ 的定义集合非空。第 42 节的有限达到论证对任意有限 Hermitian 表都成立；各项范数损失非负，故达到的总损失为零，当且仅当每项损失为零。由此

$$
\{\mathbf H:q_{\min}(\mathbf H)\le q\}
=\{\mathbf H:\Delta_q(\mathbf H)=0\}.
$$

右端是连续函数的零点集，因此闭，给出下半连续性。更具体地，若 $q_0=q_{\min}(\mathbf H)>1$，则 $\Delta_{q_0-1}(\mathbf H)>0$。只要

$$
d_1(\mathbf H,\mathbf H')
<\frac12\Delta_{q_0-1}(\mathbf H),
$$

扰动界就保证 $\Delta_{q_0-1}(\mathbf H')>0$，从而 $q_{\min}(\mathbf H')\ge q_0$。若 $q_0=1$，同一结论由维数至少为一自动成立。

这里的连续性控制最优分数与最优损失，没有把整数值的精确资源函数断言为连续。所用范数性质是 Schatten 迹范数的标准三角不等式与正算子迹公式；正且保迹映射的迹范数收缩性见 Watrous，*The Theory of Quantum Information*，[推论 3.40 及式 (3.241)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。免费经典标签上的有限达到性由第 42 节承担。证毕。

**命题 45.2（奇异权重处的维数跳变与消失损失）。** 固定命题 43.2 中的严格正定密度矩阵

$$
A=\frac18\begin{pmatrix}2&3&0\\3&5&0\\0&0&1\end{pmatrix},
\qquad
J=\frac1{27}\begin{pmatrix}5&9&0\\9&17&0\\0&0&5\end{pmatrix},
\qquad c=\frac89.
$$

对参数 $-1/2<s<1/2$，令

$$
d_s=\frac{8(4+s)}{27}>c,\qquad
H_1=D_c=cA-J,\qquad H_2(s)=D_{d_s}=d_sA-J.
$$

对每个固定 $s$，存储可以依赖 $A,J,c,d_s$，但实际采用 $c$ 还是 $d_s$ 只在存储结束后揭示。按第 41 节的两种资源口径，最小逐项无损资源为

$$
\boxed{
d_{\rm all}(s)=3\quad(-1/2<s<1/2),
\qquad
q_{\rm free}(s)=
\begin{cases}
2,&-1/2<s<0,\\
1,&0\le s<1/2.
\end{cases}
}
$$

记 $V_1(s)$ 为最优经典存储的范数总分，$\Delta(s)=\|D_c\|_1+\|D_{d_s}\|_1-V_1(s)$。则

$$
\boxed{
\begin{aligned}
&\Delta(s)=0&& (0\le s<1/2),\\
&0<\Delta(s)\le
\frac{\sqrt{36+72s+45s^2}-6-7s}{27}
&&(-1/2<s<0),
\end{aligned}
}
$$

从而 $\lim_{s\to0}\Delta(s)=0$，尽管精确无损的量子维数在 $s=0$ 发生跳变。更一般地，对任意 $q\in\{1,2,3\}$ 和同一区间中的 $s,t$，都有

$$
|V_q(s)-V_q(t)|\le\frac8{27}|s-t|,
\qquad
|\Delta_q(s)-\Delta_q(t)|\le\frac{16}{27}|s-t|.
$$

证明。候选矩阵的正定性与归一化已在命题 43.2 验证。代入得到

$$
27D_c=\operatorname{diag}(1,-2,-2),\qquad
27D_{d_s}=G_s\oplus(s-1),
$$

其中

$$
G_s=\begin{pmatrix}
3+2s&3+3s\\3+3s&3+5s
\end{pmatrix},
\qquad
\det G_s=s(s+3),\qquad
\operatorname{tr}G_s=6+7s>0.
$$

其特征值为

$$
\lambda_\pm(s)=
\frac{6+7s\pm\sqrt{36+72s+45s^2}}2.
$$

当 $s<0$ 时，$\det G_s<0$，所以前二维含一正一负两个特征值，第三个标量 $s-1$ 也严格为负。两项加权差均可逆。令 $R_s$ 为 $G_s$ 的正谱投影；其非对角元为

$$
(R_s)_{12}=\frac{3+3s}{\sqrt{36+72s+45s^2}}\ne0.
$$

故 $P_c^+=|e_1\rangle\langle e_1|$ 与 $P_{d_s}^+=R_s\oplus0$ 不对易。它们的对易子平方在前二维是某个非零负数乘 $I_2$，在第三维为零；因此生成代数包含两个中央分区，并精确为 $M_2(\mathbb C)\oplus\mathbb C$。定理 41.1 给出 $q_{\rm free}=2$ 与 $d_{\rm all}=3$。

当 $s>0$ 时，$G_s$ 的左上元与行列式都严格为正，因此 $G_s>0$，而 $s-1<0$。此时正谱投影为 $P_c^+=|e_1\rangle\langle e_1|$ 与 $P_{d_s}^+=I_2\oplus0$，生成三个一维简单块的交换代数。定理 41.1 因而给出 $q_{\rm free}=1$ 与 $d_{\rm all}=3$。$s=0$ 正是命题 43.2，其结论同样为 $q_{\rm free}=1$、$d_{\rm all}=3$，无需在奇异点使用第 41 节。

在整个参数区间，$3+2s>0$、$3+5s>0$、$s-1<0$。因此固定的标准基测量对 $D_{d_s}$ 给出的范数为

$$
\frac{(3+2s)+(3+5s)+(1-s)}{27}
=\frac{7+6s}{27},
$$

并始终保留 $\|D_c\|_1=5/27$。当 $s\ge0$ 时，$G_s$ 半正定，这个读数已经等于 $\|D_{d_s}\|_1$，故 $\Delta(s)=0$。

当 $s<0$ 时，正负特征值的绝对值之和为

$$
\|D_{d_s}\|_1
=\frac{\sqrt{36+72s+45s^2}+1-s}{27}.
$$

使用同一个标准基测量，得到其实际总损失为

$$
\frac{\sqrt{36+72s+45s^2}-6-7s}{27}.
$$

最优经典损失不大于该值。另一方面，这时精确无损要求 $q\ge2$，第 42 节的达到性排除了经典通道的最优损失为零，所以 $\Delta(s)>0$。所列上界严格为正，因为 $6+7s>0$ 且

$$
(36+72s+45s^2)-(6+7s)^2=-4s(s+3)>0.
$$

也可将它写成

$$
\frac{-4s(s+3)}
{27\left(\sqrt{36+72s+45s^2}+6+7s\right)},
$$

其分母在 $s\to0^-$ 时趋于 $324$，分子趋于零。因此最优损失从负侧也趋于零。这个上界来自一个明确可行测量，没有声称该测量在 $s<0$ 时达到最佳经典总分。

最后，对两个参数只有第二项加权差改变，并且

$$
H_2(s)-H_2(t)=\frac8{27}(s-t)A,
\qquad
d_1(\mathbf H(s),\mathbf H(t))=\frac8{27}|s-t|.
$$

定理 45.1 直接给出两条全区间扰动界。所有严格正损失均针对固定负参数；当参数接近奇异点时，这些损失没有共同的严格正下界。精确资源的整数跳变因而与最优分数的连续性相容。证毕。

<a id="entry-131"></a>

## 追加锚（新终端）

<a id="section-46"></a>

## 46. 两步参考放宽上界的完整等号域

**定理 46.1（内部严格损失、放宽最优纯输入与全部边界）。** 沿用第 29 节的两步加权任务、惰性参考、共同历史依赖系统 CPTP 控制及最终保留 $H_2R$ 的约定，限定参数域为

$$
0\le c,e\le1,\qquad 0\le g\le\frac12.
$$

记

$$
B(c;e,g)
=cg+\sqrt{\bigl[1-c(1-g)(1-2e)\bigr]^2
+4c^2(1-2g)^2e(1-e)}.
$$

则第 29 节的上界有如下完整等号判据：

$$
\boxed{
W_2(c;e,g)<B(c;e,g)
\quad\Longleftrightarrow\quad
c>0,\quad0<e<1,\quad0<g<\frac12.
}
$$

其余参数点全部取等，具体为

| 参数条件 | $W_2(c;e,g)=B(c;e,g)$ |
| --- | --- |
| $c=0$ | $1$ |
| $e=0$ | $1-c+2cg$ |
| $e=1$ | $1+c$ |
| $g=0$ | $\sqrt{(1-c)^2+4ce}$ |
| $g=1/2$ | $1+ce$ |

表中条件可以相交，交点上的表达一致。

进一步，在严格不等式的参数域中，第 29 节保留活动系统的放宽目标 $\mathcal B=B$，其最优纯输入恰为系统边缘等于 $I_2/2$ 的纯态，即系统与参考的某个二维子空间之间的最大纠缠态。任意这样的纯输入在允许的末次局部系统秩一投影测量后，都会严格损失迹范数，即使完整保留惰性参考也不例外。

原任务 $W_2$ 的最优值可以由一个参考量子比特、纯输入及两个依赖第一历史的系统幺正控制达到。本定理确定的是放宽上界的等号域，仍未给出内部参数下 $W_2$ 的一般闭式。

证明。先确定原任务优化的达到性。第 29 节已证明，第一共同系统 CPTP 控制可以吸收进自由共同输入；在 $g\le1/2$ 时，固定输入后的末次共同系统 CPTP 控制，可逐第一历史替换为使加权目标不减的系统幺正。该归约对未归一化实际分支 $c\rho$ 成立，所以覆盖本定理的全部 $c\in[0,1]$。

固定两个末次幺正 $U_0,U_1\in U(2)$。最终加权差关于输入线性，迹范数凸。对任意有限参考上的混合输入，取其有限纯态分解，至少有一个纯分量的目标值不小于混合态。因此在同时优化输入与控制时，纯输入已经足够。系统为二维，每个纯输入的 Schmidt 秩至多为二；参考等距与全部系统操作相交换，并保持最终迹范数，所以该纯输入可在一个二维参考中实现。秩一情形补零嵌入即可。

由此，$W_2$ 等于归一化纯输入 $\psi\in\mathbb C^2\otimes\mathbb C^2$ 与 $U_0,U_1\in U(2)$ 上的最大化。单位球面与两个酉群的乘积紧，最终矩阵及其迹范数对这些变量连续，因此最大值达到。这一步把任意有限参考及任意允许 CPTP 控制的上确界，化为原访问权限下的紧集优化；没有增加可操作量子记忆。

现在假设

$$
0<c\le1,\qquad0<e<1,\qquad0<g<\frac12,
\qquad a=1-g,\quad z=1-2g.
$$

在一个参考量子比特上取 Bell 态 $|\Phi\rangle=(|00\rangle+|11\rangle)/\sqrt2$。令 $T_i$ 为第 29 节放宽映射 $\mathcal F_c$ 作用于这个输入后，第一个历史 $i\in\{0,1\}$ 的差块。具体地，

$$
x_i=\frac{\sqrt{1-e}|ii\rangle+\sqrt e|1-i,1-i\rangle}{\sqrt2},
\qquad y_i=\frac{|ii\rangle}{\sqrt2},
$$

$$
T_i=cz|x_i\rangle\langle x_i|
+cgI_S\otimes\operatorname{tr}_S|x_i\rangle\langle x_i|
-|y_i\rangle\langle y_i|.
$$

在 $\operatorname{span}\{|ii\rangle,|1-i,1-i\rangle\}$ 上，其矩阵为

$$
M=\frac12\begin{pmatrix}
ca(1-e)-1&cz\sqrt{e(1-e)}\\
cz\sqrt{e(1-e)}&cae
\end{pmatrix}.
$$

另外两个正交方向 $|1-i,i\rangle$ 与 $|i,1-i\rangle$ 的特征值分别是 $cg(1-e)/2$ 与 $cge/2$，均严格为正。另一方面，

$$
\det M=\frac{ce}{4}
\left[cg(2-3g)(1-e)-(1-g)\right]<0,
$$

因为

$$
(1-g)-cg(2-3g)(1-e)
\ge1-3g+3g^2
=3\left(g-\frac12\right)^2+\frac14>0.
$$

这里使用了 $c\le1$；没有把本定理延伸到任意 $c>1$。每个 $T_i$ 因而可逆，并且有三个正特征值和一个负特征值。记其正、负谱投影为 $\Pi_i^+$、$\Pi_i^-$，则

$$
\Pi_i^++\Pi_i^-=I_4,\qquad
\Pi_i^-=|v_i\rangle\langle v_i|.
$$

矩阵 $M$ 的非对角元严格非零，故其负特征向量的两个坐标都非零。因此可以写

$$
v_i=r_i|ii\rangle+s_i|1-i,1-i\rangle,
\qquad r_is_i\ne0,
\qquad |r_i|^2+|s_i|^2=1.
$$

这说明 $v_i$ 的 Schmidt 秩为二。

接着核对放宽上界中的归一化。第 29 节给出 $\|T_0\|_1=\|T_1\|_1=B/2$。每个 $|T_i|$ 保持上述二维块与两个一维块的分解，所以 $\operatorname{tr}_S|T_i|$ 在参考的计算基中对角。又有

$$
T_1=(X\otimes X)T_0(X\otimes X),
$$

其中 $X$ 是 Pauli 交换矩阵。因此两个参考偏迹的对角元互换，得到

$$
\boxed{
\sum_{i=0}^1\operatorname{tr}_S|T_i|=\frac B2 I_R.
}
$$

这也与第 29 节的 Pauli 协变性一致。

取任意归一化纯输入，其系统边缘为 $\rho$。必要时先将参考等距嵌入维数至少二的空间。由纯化的参考等距关系及 Bell 向量恒等式，该输入在一个参考等距之前可写成

$$
|\psi_\rho\rangle
=(\sqrt{2\rho}\otimes I_R)|\Phi\rangle
=(I_S\otimes\sqrt{2\rho^{\mathsf T}})|\Phi\rangle.
$$

转置取相对于定义 Bell 态的计算基。把参考等距从最终迹范数中消去，令

$$
K_\rho=I_S\otimes\sqrt{2\rho^{\mathsf T}},
\qquad K_\rho^2=2I_S\otimes\rho^{\mathsf T}.
$$

该纯输入的第 $i$ 个放宽差块便是 $K_\rho T_iK_\rho$。将 $T_i=T_{i,+}-T_{i,-}$ 作 Jordan 分解，三角不等式与正矩阵的迹公式给出

$$
\|K_\rho T_iK_\rho\|_1
\le\operatorname{tr}(K_\rho T_{i,+}K_\rho)
+\operatorname{tr}(K_\rho T_{i,-}K_\rho)
=2\operatorname{tr}((I_S\otimes\rho^{\mathsf T})|T_i|).
$$

两历史相加，并使用偏迹恒等式，右端精确等于

$$
2\operatorname{tr}\left(\rho^{\mathsf T}\frac B2 I_R\right)=B.
$$

如果纯输入达到放宽值 $B$，两个非负的三角不等式亏差都必须为零。第 43 节关于正矩阵迹范数取等的判据说明，$K_\rho T_{i,+}K_\rho$ 与 $K_\rho T_{i,-}K_\rho$ 的支撑正交。等价地，

$$
\left\|T_{i,+}^{1/2}K_\rho^2T_{i,-}^{1/2}\right\|_2^2
=\operatorname{tr}\left(
K_\rho T_{i,+}K_\rho\,K_\rho T_{i,-}K_\rho\right)=0.
$$

由于 $T_{i,+}$ 与 $T_{i,-}$ 在各自谱支撑上严格为正，可得

$$
\Pi_i^+K_\rho^2\Pi_i^-=0.
$$

这个推论不要求 $K_\rho$ 可逆。又因 $\Pi_i^+=I_4-\Pi_i^-$，负特征向量满足

$$
(I_S\otimes\rho^{\mathsf T})v_i=\lambda v_i
$$

而成为 $I_S\otimes\rho^{\mathsf T}$ 的特征向量。对其两个系统坐标分别取分量，再用 $r_is_i\ne0$，得到

$$
\rho^{\mathsf T}|i\rangle=\lambda|i\rangle,
\qquad
\rho^{\mathsf T}|1-i\rangle=\lambda|1-i\rangle.
$$

所以 $\rho^{\mathsf T}=\lambda I_2$；由 $\operatorname{tr}\rho=1$，必有 $\rho=I_2/2$。反过来，这个边缘使 $K_\rho=I_4$，直接达到 Bell 值 $B$。因此在纯输入范围内，放宽最优输入恰好是所述最大纠缠态。这里未把一般混合态的最优性等同于它具有最大混合边缘。

再证明这些纯输入无法在原任务中保留 $B$。参考等距不改变问题，所以只需考察 Bell 输入。对第一历史 $i$，任何允许的末次系统幺正及完美指针读取，都等价于一个系统秩一 PVM $Q_i,I_S-Q_i$，随后丢弃系统而保留两结果及参考。记该 CPTP 映射为 $\mathcal C_i$。对于输出上的任意效应 $F_0\oplus F_1$，其对偶满足

$$
\mathcal C_i^*(F_0\oplus F_1)
=Q_i\otimes F_0+(I_S-Q_i)\otimes F_1.
$$

因此对偶像中的每个效应都与 $Q_i\otimes I_R$ 对易。

假设该读取保留 $T_i$ 的迹范数。取 $\mathcal C_i(T_i)$ 的最优正谱效应，并由 $\mathcal C_i^*$ 拉回。迹保持及范数等号使其成为 $T_i$ 的最优效应；$T_i$ 可逆，故由第 43 节完整最优效应区间可知，这个效应只能是 $\Pi_i^+$。于是

$$
[\Pi_i^+,Q_i\otimes I_R]=0,
\qquad
[\Pi_i^-,Q_i\otimes I_R]=0.
$$

秩一投影 $\Pi_i^-=|v_i\rangle\langle v_i|$ 与另一投影对易，意味着 $v_i$ 属于后者的值域或核。这里两者分别为

$$
\operatorname{ran}Q_i\otimes\mathbb C^2,
\qquad
\operatorname{ran}(I_S-Q_i)\otimes\mathbb C^2.
$$

系统因子在任一子空间内都为一维，所以其中每个向量的 Schmidt 秩至多为一。这与 $v_i$ 的 Schmidt 秩为二矛盾。因此每个第一历史上的局部读取都严格损失迹范数。

原任务的最大值已经由某个纯输入及两个末次幺正达到。如果其值等于 $B$，则第 29 节共同后处理的收缩链强制该纯输入先达到放宽值 $B$，从而必须是上述最大纠缠态。但刚证明这种输入经过末次局部读取后严格损失，矛盾。故在所列内部参数域有 $W_2<B$。紧集达到性在这里是必要的一环：只证明每个固定协议不取等，尚不足以排除一列协议趋近 $B$。

最后验证其余所有参数点的达到构造。以下协议均符合原系统控制权限，且不使用参考。由于第 29 节始终给出 $W_2\le B$，逐项达到相应 $B$ 就足以确定精确值。

当 $c=0$ 时，加权差仅为归一化理想输出的负值，迹范数恒为一，等于 $B=1$。

当 $e=0$ 时，取指针输入 $|0\rangle$，所有控制恒等。第一历史必为 $0$，理想完整历史为 $00$；实际末次两个结果概率为 $1-g$、$g$。因为 $c(1-g)\le1$，加权绝对值之和为

$$
|c(1-g)-1|+cg=1-c+2cg=B(c;0,g).
$$

当 $e=1$ 时，同样取指针输入及恒等控制。理想第一历史为 $0$，实际第一历史为 $1$，完整输出支持已经分离，后续读取不改变这一点。因此加权差的迹范数为 $1+c=B(c;1,g)$。

当 $g=1/2$ 时，继续使用指针输入及恒等控制。理想完整历史为 $00$；实际四个历史 $00,01,10,11$ 的概率依次为

$$
\frac{1-e}{2},\quad\frac{1-e}{2},\quad
\frac e2,\quad\frac e2.
$$

由 $c(1-e)/2\le1$，加权范数为

$$
\left|\frac{c(1-e)}2-1\right|
+\frac{c(1-e)}2+ce=1+ce=B(c;e,1/2).
$$

当 $g=0$ 时，取无参考输入 $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$，第一控制恒等。记

$$
x_i=K_i|+\rangle,
\qquad y_i=P_i|+\rangle,
\qquad H_i=c|x_i\rangle\langle x_i|-|y_i\rangle\langle y_i|,
$$

其中 $K_i$ 与指针投影 $P_i$ 沿用第 29 节。对每个第一历史选择共同系统幺正，使 $H_i$ 在末次指针基中对角。因为末次读取无错误，这个合法协议得到的加权范数恰为 $\sum_i\|H_i\|_1$。两个矩阵酉等价，其中一个为

$$
H_0=\frac12\begin{pmatrix}
c(1-e)-1&c\sqrt{e(1-e)}\\
c\sqrt{e(1-e)}&ce
\end{pmatrix}.
$$

它的迹为 $(c-1)/2$，行列式为 $-ce/4$，故

$$
\|H_0\|_1=\frac12\sqrt{(1-c)^2+4ce}.
$$

当 $ce=0$ 时，同一式由直接计算成立。两历史相加就达到

$$
\sqrt{(1-c)^2+4ce}=B(c;e,0).
$$

这些边界穷尽闭参数域中不满足严格条件的点，并证明表中全部表达。各边界均存在取等点，因此没有从上述内部严格性得到跨整个参数域的统一正差距。

所用 Choi 与纯输入变换属于标准表示理论。Watrous，*Simpler semidefinite programs for completely bounded norms*，[§3.1，式 (10) 与 Theorem 6](https://arxiv.org/html/1207.5726) 给出向量化、转置及 Choi 夹乘公式；该文使用未归一化 Choi 算子，而本节 $\bigoplus_iT_i$ 来自归一化 Bell 态，因此两者相差输入维数因子二。可逆差的最优效应唯一性是量子 Neyman–Pearson 引理的特例，见 Jenčová，*Reversibility conditions for quantum operations*，[Lemma 7](https://arxiv.org/abs/1107.0453)，其完整效应区间已在第 43 节使用。本节结合第 29 节的具体差块，分析放宽取等强制的输入结构与末次局部读取的障碍；原目标内部的一般精确值仍未求出。证毕。

<a id="entry-133"></a>

## 追加锚（新终端）

<a id="section-47"></a>

## 47. 第一次读取前固定 Bell 有效输入的两步精确值

**定义 47.1（固定 Bell 有效输入的加权任务）。** 沿用定义 29.1 的两步加权任务、惰性参考和末端丢弃活动系统的约定。将第一共同控制吸收进有效输入后，额外要求第一次仪器作用前的共同输入直接固定为

$$
|\Phi\rangle_{SR}=\frac{|00\rangle+|11\rangle}{\sqrt2}.
$$

在两次读取之间，仍允许依赖第一历史 $i$ 的任意共同系统 CPTP 控制，控制环境丢弃后不可再次访问；参考 $R$ 不受控制。记这一受限任务的值为

$$
W_2^{\Phi}(c;e,g)
=\sup_{\{\mathcal C_i\}_{i=0}^1}
\sum_{i,j=0}^1\|cX_{ij}^{\Phi}-Q_{ij}^{\Phi}\|_1.
$$

这里 $X_{ij}^{\Phi}$、$Q_{ij}^{\Phi}$ 分别是实际与理想协议在相同控制表下产生的未归一化参考块。固定有效输入意味着在 $|\Phi\rangle$ 与第一次仪器之间没有额外可优化的共同 CPTP 控制；它与“先提供 Bell 态、再允许任意前置 CPTP 控制”的任务不同。

**定理 47.2（固定 Bell 有效输入的精确值与最优控制）。** 对

$$
c=\frac7{20},\qquad e=\frac3{10},\qquad g=\frac1{10},
$$

定义 47.1 的最优值为

$$
W_2^{\Phi}\left(\frac7{20};\frac3{10},\frac1{10}\right)
=\frac{909}{1000}.
$$

两条第一历史均取恒等的中间系统控制即可达到该值。将固定有效输入换成任意纯最大纠缠系统—参考态，最优值仍相同。

证明。定理 29.2 对末次共同 CPTP 控制的逐历史归约适用于固定输入：因 $g\le1/2$，可将每个中间控制换成一个共同系统幺正而使当前加权目标不减。因此只需对两条历史各自优化一个系统秩一投影测量，并在读出第二结果后丢弃系统。

先处理第一历史 $i=0$。设第二次完美读取所对应的系统效应为

$$
E_0=
\begin{pmatrix}
q&\xi\sqrt{q(1-q)}\\
\overline\xi\sqrt{q(1-q)}&1-q
\end{pmatrix},
\qquad E_1=I-E_0,
\qquad 0\le q\le1,\quad |\xi|=1.
$$

端点 $q=0,1$ 的相位可任取。令 $z=1-2g$。定理 29.2 的共同后处理表达表明，加权参考差块为

$$
cX_{0j}^{\Phi}-Q_{0j}^{\Phi}
=\frac12\left[cK_0(gI+zE_j)K_0-P_0E_jP_0\right]^{\mathsf T}.
$$

转置不改变迹范数。代入指定参数，对 $j=0$，括号中的矩阵可写为

$$
M(q,\xi)=
\begin{pmatrix}
\displaystyle\frac{49}{2000}-\frac{201}{250}q
&\displaystyle\xi\sqrt{\frac{1029}{62500}q(1-q)}\\
\displaystyle\overline\xi\sqrt{\frac{1029}{62500}q(1-q)}
&\displaystyle\frac{189}{2000}-\frac{21}{250}q
\end{pmatrix}.
$$

对 $j=1$，矩阵是 $M(1-q,-\xi)$。Hermitian 二阶矩阵的特征值只依赖对角元及非对角元的模，所以

$$
h(q):=\|M(q,\xi)\|_1
$$

与 $\xi$ 无关。第一历史 $i=0$ 的目标贡献为 $[h(q)+h(1-q)]/2$。第一历史 $i=1$ 由同时交换系统与参考的两个基向量得到，具有相同的可取贡献集合。两个历史的控制可独立选择，故

$$
W_2^{\Phi}\left(\frac7{20};\frac3{10},\frac1{10}\right)
=\max_{0\le q\le1}\bigl[h(q)+h(1-q)\bigr].
$$

下面求这个一变量最大值。直接展开得

$$
\operatorname{tr}M(q,\xi)
=t(q):=\frac{119}{1000}-\frac{111}{125}q,
$$

$$
\det M(q,\xi)
=\frac{21}{4000000}\bigl(16000q^2-18000q+441\bigr).
$$

行列式的两个零点为

$$
q_* =\frac9{16}-\frac{3\sqrt{5135}}{400},
\qquad
q^* =\frac9{16}+\frac{3\sqrt{5135}}{400}.
$$

由 $71<\sqrt{5135}<72$，可知

$$
0<q_*<\frac12<1<q^*.
$$

矩阵右下对角元在 $0\le q\le1$ 上至少为 $21/2000>0$。因此，当 $0\le q\le q_*$ 时，$M(q,\xi)$ 半正定，迹范数等于 $t(q)$；当 $q_*<q\le1$ 时，行列式为负，两特征值异号，迹范数等于其间距。令

$$
R(q)=\frac{113136q^2+41664q+1225}{250000},
\qquad f(q)=\sqrt{R(q)}.
$$

则

$$
h(q)=
\begin{cases}
t(q),&0\le q\le q_*,\\
f(q),&q_*\le q\le1.
\end{cases}
$$

在 $q=q_*$ 两式相等。$R$ 的常数项为正，其一次、二次系数亦为正，因此 $f$ 在 $[0,1]$ 上严格递增。若将 $R(q)$ 写成 $a_2q^2+a_1q+a_0$，则

$$
4a_2a_0-a_1^2
=-\frac{18461289}{976562500}<0,
$$

而

$$
f''(q)=\frac{4a_2a_0-a_1^2}{4R(q)^{3/2}}<0.
$$

故 $f$ 在整个区间上严格凹。

目标关于 $q\leftrightarrow1-q$ 对称，只需考虑 $0\le q\le1/2$。若 $0\le q\le q_*$，则

$$
h(q)+h(1-q)=t(q)+f(1-q).
$$

$t(q)$ 严格递减，$f(1-q)$ 也严格递减，所以该区间的最大值在 $q=0$，等于

$$
h(0)+h(1)=\frac{119}{1000}+\frac{79}{100}
=\frac{909}{1000}.
$$

若 $q_*\le q\le1/2$，则 $q$ 与 $1-q$ 都位于根式分支。由 $f$ 的凹性，

$$
h(q)+h(1-q)
=f(q)+f(1-q)
\le2f\left(\frac12\right)
=\frac{\sqrt{50341}}{250}.
$$

两个比较量都为正，且

$$
\left(\frac{909}{1000}\right)^2
-\left(\frac{\sqrt{50341}}{250}\right)^2
=\frac{833}{40000}>0.
$$

因此全局最大值为 $909/1000$，在 $q=0,1$ 达到。恒等中间控制在每条第一历史都给出这类端点投影，故达到所述值。

最后，任意纯最大纠缠系统—参考态都可写成

$$
(I_S\otimes V_R)|\Phi\rangle,
$$

其中 $V_R$ 是从一个参考量子比特到实际参考空间的等距映射。全部允许操作只作用于系统，因此其输出参考块与 Bell 输入的输出块相差同一个参考等距嵌入，迹范数不变。故最优值相同。

本证明的模型归约与共同后处理直接使用定理 29.2；二阶谱计算随后给出固定有效输入的精确最大值。迹范数判别的标准背景可见 Ballester、Wehner 与 Winter，*State Discrimination with Post-Measurement Information*，[Theorem 2.1](https://arxiv.org/abs/quant-ph/0608014)；末段所用纯化的参考酉等价见 Watrous，*The Theory of Quantum Information*，[Theorem 2.12](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。不同参考维数先限制到 Schmidt 支撑并等距嵌入同维空间即可应用该等价。上述标准结果提供迹范数与纯化工具，本节的 $909/1000$ 则由已列的一变量最大化直接求得。证毕。

**命题 47.3（原两步任务的 Bell 有效输入并非最优）。** 在定理 47.2 的参数点，原任务满足

$$
W_2^{\Phi}\left(\frac7{20};\frac3{10},\frac1{10}\right)
=\frac{909}{1000}
<\frac{\sqrt{534}}{25}
\le W_2\left(\frac7{20};\frac3{10},\frac1{10}\right)
<\frac7{200}+\frac{\sqrt{207433}}{500}.
$$

因此，第 29 章放宽任务的 Bell 达到性不能推出原任务存在最大纠缠的最优有效输入。这一严格比较不确定原任务 $W_2$ 的完整最优值。

证明。定理 29.2 的无参考输入 $|+\rangle$ 及按历史选择的共同幺正控制达到 $\sqrt{534}/25$，因而给出原任务的下界。定理 47.2 给出受限 Bell 任务的精确值。指定参数位于定理 46.1 的严格域，故原任务严格小于第 29 节的放宽上界，得到链的最后一个不等式。Bell 值与无参考下界均为正，且

$$
\left(\frac{\sqrt{534}}{25}\right)^2
-\left(\frac{909}{1000}\right)^2
=\frac{28119}{1000000}>0.
$$

所以每个纯最大纠缠有效输入的最佳值都严格小于一个允许的无参考协议值，不能达到原任务的最优值。上述论证没有给出 $W_2$ 等于该下界的上界证明，故不确定其完整值。证毕。

<a id="entry-135"></a>

## 追加锚（新终端）
<a id="section-48"></a>

## 48. 半错误首步下的一族精确参考优势区域

**定义 48.1（Hadamard 与指针控制的 Schmidt 输入族）。** 沿用第 29 节的加权两步任务，固定第一步参数 $e=1/2$，并取

$$
0<c\le1,\qquad0<g<\frac12,\qquad0\le p\le1.
$$

准备一个活动系统量子比特及一个惰性参考量子比特，其共同有效输入为

$$
|\psi_p\rangle_{SR}
=\sqrt p\,|00\rangle+\sqrt{1-p}\,|11\rangle.
$$

第一共同控制恒等；第一次结果为 $0$ 时，第二共同系统控制取 Hadamard 矩阵 $H$；第一次结果为 $1$ 时取恒等矩阵 $I_2$。后者也可换成 Pauli 矩阵 $X$，这只交换该历史的两个末次结果。两种候选使用同一控制表，参考从制备后到最终观察前始终不受操作，末端丢弃活动系统，保留全部经典历史与参考。记这个指定协议的加权迹范数分数为 $F(c,g,p)$。

**定理 48.2（协议精确值与相对无参考最优值的完整优势判据）。** 在定义 48.1 的参数域内，令

$$
a=1-g,\qquad z=1-2g,\qquad b=1-ca>0,
$$

$$
L(p)=1-\frac{cz}{2}-bp,
\qquad
R(p)=\left(\frac c2-p\right)^2
+p(1-p)\left[2c-c^2(1-z^2)\right].
$$

则协议分数精确为

$$
\boxed{F(c,g,p)=L(p)+\sqrt{R(p)}.}
$$

第 30 节的全部无参考输入及共同系统 CPTP 控制最优值在本切片化为

$$
\boxed{
C(c,g):=W_2^{\mathrm{cl}}(c;1/2,g)
=\max\{P,S\},
\qquad
P=1+cg,\quad S=\sqrt{1+c^2z^2}.
}
$$

为比较两者，定义

$$
J=2g+ca(1-5g)>0,\qquad u=a(1-4g),
\qquad h=\max\{0,S-P\},
$$

$$
D=c^2u-2bh,\qquad
\mathcal D=D^2-4cJh(c+h).
$$

对任意给定 $p\in[0,1]$，有精确等价

$$
\boxed{
F(c,g,p)>C(c,g)
\quad\Longleftrightarrow\quad
-cJp^2+Dp-h(c+h)>0.
}
$$

因此，存在严格优于全部无参考协议的输入参数 $p$，当且仅当

$$
\boxed{D>0\quad\text{且}\quad\mathcal D>0.}
$$

这两个条件成立时，全部严格优势参数恰为

$$
\boxed{
p\in(p_-,p_+),\qquad
p_\pm=\frac{D\pm\sqrt{\mathcal D}}{2cJ},
\qquad0\le p_-<p_+<1.
}
$$

若 $P\ge S$，判据进一步简化为

$$
\boxed{
F(c,g,p)>C(c,g)
\quad\Longleftrightarrow\quad
0<g<\frac14,\qquad
0<p<\frac{ca(1-4g)}{2g+ca(1-5g)}.
}
$$

其中 $P\ge S$ 本身等价于

$$
2g\ge c(1-g)(1-3g).
$$

若 $g\ge1/4$，本协议族对任何 $c,p$ 都不能超过无参考最优值。这个结论只限制定义 48.1 的输入与控制族，不排除其他参考协议的优势，也未求出一般 $W_2(c;1/2,g)$ 的最优值。

证明。因为 $e=1/2$，实际第一步的两个 Kraus 算子均为 $I_2/\sqrt2$，理想第一步的算子为指针投影 $P_i=|i\rangle\langle i|$。末次实际效应为 $gI_2+zP_j$。对给定系统控制 $U_i$，相应的初始系统差效应为

$$
M_{ij}=\frac c2U_i^\dagger(gI_2+zP_j)U_i
-P_iU_i^\dagger P_jU_iP_i.
$$

记 $\rho_p=\operatorname{diag}(p,1-p)$。由 Schmidt 输入的直接展开，最终历史 $ij$ 的未归一化参考差块是

$$
N_{ij}=\sqrt{\rho_p}\,M_{ij}^{\mathsf T}\sqrt{\rho_p}.
$$

这里没有对任何分支重新归一化。不同经典历史的块正交，故 $F=\sum_{i,j}\|N_{ij}\|_1$。

当第一结果为 $0$ 时，$U_0=H$ 给出

$$
N_{00}=\frac14\begin{pmatrix}
(c-2)p&cz\sqrt{p(1-p)}\\
cz\sqrt{p(1-p)}&c(1-p)
\end{pmatrix},
$$

$$
N_{01}=\frac14\begin{pmatrix}
(c-2)p&-cz\sqrt{p(1-p)}\\
-cz\sqrt{p(1-p)}&c(1-p)
\end{pmatrix}.
$$

它们的行列式同为

$$
\frac{cp(1-p)}{16}\left[c(1-z^2)-2\right].
$$

由于 $0<c\le1$ 和 $0<z<1$，括号严格为负。对 $0<p<1$，两个矩阵都严格不定，迹范数等于特征值间距，因此

$$
\|N_{00}\|_1+\|N_{01}\|_1
=\frac12\sqrt{\left[c+2(1-c)p\right]^2
+4c^2z^2p(1-p)}
=\sqrt{R(p)}.
$$

最后一式由展开得到。在 $p=0,1$ 时，直接计算两个对角矩阵也给出同一公式。

当第一结果为 $1$ 时，$U_1=I_2$ 给出

$$
N_{10}=\operatorname{diag}\left(\frac{cap}{2},\frac{cg(1-p)}2\right),
$$

$$
N_{11}=\operatorname{diag}\left(\frac{cgp}{2},
\left(\frac{ca}{2}-1\right)(1-p)\right).
$$

第一块半正定，第二块的两个对角元分别非负、非正。相加得到

$$
\|N_{10}\|_1+\|N_{11}\|_1
=\frac{cp}{2}+\left(1-\frac{cz}{2}\right)(1-p)
=L(p).
$$

若取 $U_1=X$，两个块只交换，迹范数之和不变。这证明协议的精确分数。四块的总迹为 $c-1$，与实际及理想完整输出的归一化一致；整个计算保留全部历史，没有后选择。

接着计算无参考比较值。将 $e=1/2$ 代入定理 30.2，令该节的 $d=cz$，则 $0<d<1$，而 $r=0$、$v=1$，从而

$$
\eta=\frac{4(1-d)}{2-d}>0.
$$

因此该节的第三个内部候选不出现，无参考最优值就是其端点候选 $P=1+cg$ 与对称候选 $S=\sqrt{1+c^2z^2}$ 的最大值。两者都严格为正，直接平方得

$$
P^2-S^2
=c\left[2g-c(1-g)(1-3g)\right].
$$

由 $c>0$，这给出陈述中的 $P\ge S$ 判据。

为了安全地比较根式，注意

$$
C=P+h,\qquad
C-L(p)=\frac c2+bp+h>0.
$$

因此 $F>C$ 等价于 $R(p)>(C-L(p))^2$，平方没有引入额外解。展开协议根式与端点比较值，得到

$$
R(p)-(P-L(p))^2
=cp\left[ca(1-4g)-Jp\right].
$$

再把比较值从 $P$ 改为 $P+h$，便有

$$
\begin{aligned}
R(p)-(C-L(p))^2
&=cp\left[ca(1-4g)-Jp\right]
-2h\left(\frac c2+bp\right)-h^2\\
&=-cJp^2+Dp-h(c+h).
\end{aligned}
$$

这证明逐 $p$ 的精确等价。

还需证明二次不等式的参数条件确实与 $p\in[0,1]$ 相容。首先，

$$
J=2g(1-c)+c(1-4g+5g^2),\qquad
1-4g+5g^2=5\left(g-\frac25\right)^2+\frac15>0,
$$

所以 $J>0$。相应二次函数严格凹，常数项为 $-h(c+h)\le0$。若 $D\le0$，它在 $p\ge0$ 上不可能为正；若 $D>0$ 而 $\mathcal D\le0$，其全实轴最大值也不为正。因而存在优势参数必须有 $D>0$、$\mathcal D>0$。

反过来，假设这两个条件成立。由 $D=c^2u-2bh>0$、$b>0$、$h\ge0$，必有 $u>0$，即 $g<1/4$。定义

$$
p_P=\frac{cu}{J}=\frac{ca(1-4g)}{J}.
$$

它满足

$$
0<p_P<1,
\qquad
J-cu=g(2-ca)>0.
$$

二次函数的顶点在

$$
p_{\rm v}=\frac D{2cJ}\in\left(0,\frac{p_P}{2}\right].
$$

$\mathcal D>0$ 使顶点值严格为正，因此它已在 $(0,1)$ 内取得正值。两个实根为陈述中的 $p_-,p_+$。根的和为正、积为 $h(c+h)/(cJ)\ge0$，故 $p_-\ge0$。若 $h=0$，两根直接是 $0,p_P$；若 $h>0$，二次函数在 $p=p_P$ 处的值为

$$
-h(c+2bp_P+h)<0.
$$

结合顶点位于 $p_P/2$ 之前，可知 $0<p_-<p_+<p_P<1$。所以在所有情形下，严格优势参数精确为 $(p_-,p_+)$，并且无需与 $[0,1]$ 再作未知的截取。

若 $P\ge S$，则 $h=0$。优势二次式退化为 $cp(cu-Jp)$，立即得到 $g<1/4$ 及 $0<p<p_P$ 的简化条件。若 $g\ge1/4$，则 $u\le0$、$D\le0$，故本协议不可能严格超过 $C$；这没有对优化域中其他参考控制作断言。

也可核对几个退化边界。$p=0$ 时 $F=P\le C$，$p=1$ 时 $F=1<C$。连续延拓到 $c=0$ 时，$F=C=1$；此时不使用根区间中的除法。延拓到 $g=1/2$ 时，有 $F=1+c/2-cp/2\le C=1+c/2$。在 $g=0$ 时，第 29 节放宽上界与第 30 节无参考值同为 $\sqrt{1+c^2}$；已有无参考协议达到该值，所以本协议也不可能产生严格参考优势。这些边界核对没有把上述开参数域的根公式用于零分母。

协议差块的构造沿用第 21 节的参考输出公式及第 23 节的二阶 Hermitian 迹范数计算；全部无参考优化由定理 30.2 承担。二元判别中迹范数与最优成功概率的标准关系见 Ballester、Wehner 与 Winter，*State Discrimination with Post-Measurement Information*，[Theorem 2.1](https://arxiv.org/html/quant-ph/0608014)，其中归于 Helstrom。本节精确比较的是一个明确参考协议族与已经优化的无参考任务，不把协议族的存在优势判据当作一般参考任务的完整分类。证毕。

**推论 48.3（整段参数上的严格参考增益及三步应用）。** 令

$$
g_0=1-\frac{\sqrt6}{3}.
$$

对任意

$$
g_0\le g<\frac14,\qquad0<c\le1,
$$

都有 $C(c,g)=1+cg$，并且非空区间

$$
0<p<\frac{c(1-g)(1-4g)}
{2g+c(1-g)(1-5g)}
$$

中的每个参数都给出

$$
W_2(c;1/2,g)\ge F(c,g,p)
>W_2^{\mathrm{cl}}(c;1/2,g).
$$

特别地，$g=1/5$ 时，这个区间精确化为 $0<p<2c/5$。

进一步，对任意 $g\in[g_0,1/4)$ 与末次参数 $f\in[1/2,1)$，三步系统 CPTP 任务满足

$$
\boxed{
T_3^{\mathrm{ref,CPTP}}(1/2,g,f)
>T_3^{\mathrm{cl,CPTP}}(1/2,g,f).
}
$$

这里的参考仍然是惰性的，没有额外可操作量子记忆。对每个选定的参数，可以用上述一个参考量子比特的输入与控制族，再接第 28 节的共同尾段构造，得到严格优于全部无参考系统 CPTP 协议的三步值。

证明。首先 $0<g_0<1/4$：前一式由 $\sqrt6<3$ 得到，后一式等价于 $\sqrt6>9/4$，平方后为 $6>81/16$。在所列区间内，$1-3g>0$。由于 $c\le1$，有

$$
\begin{aligned}
2g-c(1-g)(1-3g)
&\ge2g-(1-g)(1-3g)\\
&=-1+6g-3g^2\ge0.
\end{aligned}
$$

最后一步来自该二次式的较小根 $g_0$，且整个当前区间在较大根 $1+\sqrt6/3$ 之前。因此 $P\ge S$，即 $C=1+cg$。又因 $g<1/4$，定理 48.2 的 $p_P$ 严格为正且小于一，所列区间非空，并且每个其中的 $p$ 都产生严格优势。这个协议属于原参考优化域，所以 $W_2\ge F$。

在 $g=1/5$ 时，$a=4/5$、$1-4g=1/5$、$1-5g=0$，因而 $p_P=2c/5$；相应的平方比较是

$$
R(p)-(P-L(p))^2=\frac{2cp(2c-5p)}{25}.
$$

这说明第 21 节的孤立优势构造位于一个连续参数族中。

现在取 $f\in[1/2,1)$，令 $c=1-f\in(0,1/2]$。第 28 节的加权尾段归约与第 30 节的无参考版本分别给出

$$
T_3^{\mathrm{ref,CPTP}}(1/2,g,f)
=\frac f2+\frac12W_2(1-f;1/2,g),
$$

$$
T_3^{\mathrm{cl,CPTP}}(1/2,g,f)
=\frac f2+\frac12C(1-f,g).
$$

对上面非空区间中的任意 $p$，将严格两步优势代入得到

$$
\begin{aligned}
T_3^{\mathrm{ref,CPTP}}(1/2,g,f)
&\ge\frac f2+\frac12F(1-f,g,p)\\
&>\frac f2+\frac12C(1-f,g)
=T_3^{\mathrm{cl,CPTP}}(1/2,g,f).
\end{aligned}
$$

第 28 节的达到方向把这个指定两步协议接成允许的共同系统 CPTP 尾段，因此严格不等式对应可实现的参考协议。端点 $f=1$ 会使 $c=0$，已在前一定理的边界讨论中排除严格优势，故本推论不包含它。这里仍未求出三步参考任务的完整精确值。证毕。
<a id="section-49"></a>

## 49. 两步惰性参考任务中两个固定读取轴不足的精确反例

**定义 49.1（固定读取轴菜单）。** 沿用第 29 节的两步加权任务，取

$$
c=\frac45,\qquad e=\frac12,\qquad g=\frac1{20}.
$$

第一共同控制吸收进有效输入，允许任意有限惰性参考及任意归一化共同输入。末次共同系统控制限制为幺正，并要求每个第一历史 $i$ 对应的末次完美读取效应，只能选以下两种互补秩一 PVM 之一：

$$
\mathsf Z=\{P_0,P_1\},
\qquad
\mathsf X=\{|+\rangle\langle+|,|-\rangle\langle-|\}.
$$

每条第一历史独立选轴，末次结果可以重标记。完美读取效应指第 29 节将最后一次有误仪器改写成退极化后处理之后的效应；有误参数 $g=1/20$ 保留不变。活动系统最后丢弃，保留完整两次历史及参考。将这一菜单下的最优加权迹范数记为 $W_{\{\mathsf X,\mathsf Z\}}$。由于 $g\le1/2$，第 29 节的逐历史归约说明，在同一菜单效应约束下允许末次 CPTP 控制所得的值与允许共同系统幺正所得的值相同；以下直接使用幺正实现。

**引理 49.2（固定控制表的纯化目标对系统边缘凹）。** 固定一个允许的历史控制表，并将对应实际与理想输出映射的加权差记为 Hermitian 保持映射 $\mathcal F$。对系统密度矩阵 $\rho$，令

$$
f_{\mathcal F}(\rho)
=\| (\mathcal F\otimes\operatorname{id})(|\psi_\rho\rangle\langle\psi_\rho|)\|_1,
$$

其中 $|\psi_\rho\rangle$ 为任意纯化，纯化参考始终不受控制。则 $f_{\mathcal F}$ 良定义，并且为凹函数。

证明。同一系统边缘的纯化之间可通过参考等距联系。所有协议映射只作用于系统，参考等距保留输出迹范数，因此选择纯化不影响数值。

设 $\rho=\lambda\rho_0+(1-\lambda)\rho_1$，其中 $0\le\lambda\le1$。把两种纯化嵌入同一个有限参考空间，并引入一个仅用于纯化的二标签参考因子 $F$，取

$$
|\Omega\rangle
=\sqrt\lambda\,|\psi_{\rho_0}\rangle|0\rangle_F
+\sqrt{1-\lambda}\,|\psi_{\rho_1}\rangle|1\rangle_F.
$$

它是 $\rho$ 的归一化纯化。在输出参考因子 $F$ 上去相干，产生两个权重分别为 $\lambda$、$1-\lambda$ 的直和块，故去相干后的迹范数为

$$
\lambda f_{\mathcal F}(\rho_0)+(1-\lambda)f_{\mathcal F}(\rho_1).
$$

去相干是 CPTP 映射，在 Hermitian 算子上收缩迹范数。因此

$$
f_{\mathcal F}(\rho)
\ge\lambda f_{\mathcal F}(\rho_0)+(1-\lambda)f_{\mathcal F}(\rho_1).
$$

这里的参考去相干只用于比较两个输出范数，并未作为控制操作加入原协议。证毕。

**定理 49.3（菜单的精确值与菜单外的严格增益）。** 在上述定义中，

$$
W_{\{\mathsf X,\mathsf Z\}}=\frac{\sqrt{949}}{25}.
$$

另有一个只用参考量子比特、纯有效输入及两个实幺正系统控制的允许协议，其值为

$$
\frac{\sqrt{479942241}+\sqrt{910376791}}{42250}
>\frac{\sqrt{949}}{25}.
$$

因此，将两个末次系统读取轴限制为 $\mathsf X$、$\mathsf Z$ 会严格降低原任务的最优值，即使菜单内允许任意输入和任意有限惰性参考。这一结论不确定原任务的完整最优值，也不声称排除所有系统边缘对角的输入。

证明。固定菜单内的一个控制表。最终加权差关于共同输入线性，迹范数凸，所以某个纯态分量的值不低于混合输入。纯输入的 Schmidt 秩至多二，可将参考等距压缩至量子比特，并用其系统边缘 $\rho$ 参数化。

因为 $e=1/2$，第一次实际 Kraus 算子均为 $K_i=I/\sqrt2$。令 $z=1-2g=9/10$。对第一历史 $i$ 和末次效应 $E_{ij}$，定义初始系统差效应

$$
M_{ij}=\frac c2(gI+zE_{ij})-P_iE_{ij}P_i.
$$

选取规范纯化后，第 23 节的参考部分迹公式给出目标

$$
f(\rho)=\sum_{i,j}\|\sqrt\rho\,M_{ij}\sqrt\rho\|_1.
$$

参考输出中的转置不改变迹范数。这个 $f$ 正是引理中固定整个控制表的函数，因此对 $\rho$ 凹。

令 $Z=\operatorname{diag}(1,-1)$。若第一历史 $i$ 选择 $\mathsf Z$，则 $ZM_{ij}Z=M_{ij}$。若它选择 $\mathsf X$，则 $ZE_{ij}Z=E_{i,1-j}$，且 $P_iE_{ij}P_i=P_i/2$，从而

$$
ZM_{ij}Z=M_{i,1-j}.
$$

所以对每个固定表都有 $f(Z\rho Z)=f(\rho)$：第一历史保持不变，仅在选择 $\mathsf X$ 的分支内互换末次结果。凹性给出

$$
f\left(\frac{\rho+Z\rho Z}{2}\right)\ge f(\rho).
$$

因此，每个固定菜单表的最优值都可用

$$
\rho_p=\operatorname{diag}(p,1-p),\qquad0\le p\le1
$$

达到。以下枚举的是全部四张菜单表及其连续输入优化。

两条第一历史均选择 $\mathsf Z$ 时，全部参考差块对角，直接求绝对值之和得到

$$
f_{\mathsf Z\mathsf Z}(\rho_p)=1+cg=\frac{26}{25}.
$$

两条第一历史均选择 $\mathsf X$ 时，同时交换系统两个计算基向量只会交换第一历史，故

$$
f_{\mathsf X\mathsf X}(\rho_p)
=f_{\mathsf X\mathsf X}(\rho_{1-p}).
$$

再用引理的凹性，其最大值在 $p=1/2$。在此输入上直接计算两阶块的两特征值间距，得到

$$
f_{\mathsf X\mathsf X}(I/2)
=\sqrt{1+c^2z^2}=\frac{\sqrt{949}}{25}.
$$

如果第一历史 $0$ 选择 $\mathsf X$、第一历史 $1$ 选择 $\mathsf Z$，用二阶矩阵公式

$$
\|\sqrt\rho M\sqrt\rho\|_1
=\sqrt{[\operatorname{tr}(\rho M)]^2-4\det\rho\det M}
\quad\text{当 }\det M<0
$$

及半定块的绝对迹公式，得到

$$
f_{\mathsf X\mathsf Z}(\rho_p)
=\frac{16-6p+\sqrt{-299p^2+424p+100}}{25}.
$$

具体地，$\mathsf X$ 分支的两个块各有相同的迹范数，其和为式中的根式除以 $25$；$\mathsf Z$ 分支的范数为 $(16-6p)/25$。交换两条第一历史对应 $p\leftrightarrow1-p$，所以另一张混合表具有同一最优值。

对全部 $p\in[0,1]$，$14+6p>0$，并且

$$
\begin{aligned}
(14+6p)^2-(-299p^2+424p+100)
&=335p^2-256p+96\\
&=335\left(p-\frac{128}{335}\right)^2
+\frac{15776}{335}>0.
\end{aligned}
$$

故混合表的目标严格小于 $30/25$。由于

$$
26<30<\sqrt{949},
$$

四张表中最大值由 $\mathsf X\mathsf X$ 和 Bell 输入达到，为 $\sqrt{949}/25$。输入、参考和菜单控制的上界均已覆盖。 这里的凹性与 $Z$ 共轭只对每一张固定菜单表成立；先对控制表取上确界后所得函数不必仍然凹，因此该论证不外推到原任务的连续控制全体。

现在构造菜单外的协议。取系统边缘

$$
\rho=\begin{pmatrix}\frac12&\frac7{20}\\\frac7{20}&\frac12\end{pmatrix},
\qquad\det\rho=\frac{51}{400},
$$

并取其纯化

$$
|\psi\rangle
=\sqrt{\frac{17}{20}}\,|++\rangle
+\sqrt{\frac3{20}}\,|--\rangle.
$$

这个态归一化，参考保持惰性。对第一历史 $0$，选择末次第零结果效应

$$
Q=\frac1{169}\begin{pmatrix}144&-60\\-60&25\end{pmatrix},
$$

另一效应为 $I-Q$。$Q$ 是实秩一投影，因为它投影到归一化向量 $(12,-5)^{\mathsf T}/13$。对第一历史 $1$ 选择效应 $XQX$、$I-XQX$，其中 $X$ 是 Pauli 交换矩阵。这些实秩一 PVM 均由允许的实幺正中间控制实现。

第一历史 $0$ 的两个初始系统差效应为

$$
M_{00}=\frac1{8450}\begin{pmatrix}-4439&-1080\\-1080&619\end{pmatrix},
\qquad
M_{01}=\frac1{8450}\begin{pmatrix}-631&1080\\1080&2761\end{pmatrix}.
$$

它们的行列式分别是

$$
\det M_{00}=-\frac{3914141}{71402500},
\qquad
\det M_{01}=-\frac{2908591}{71402500},
$$

并且

$$
\operatorname{tr}(\rho M_{00})=-\frac{1333}{4225},
\qquad
\operatorname{tr}(\rho M_{01})=\frac{1821}{8450}.
$$

故二阶谱公式给出

$$
\|\sqrt\rho M_{00}\sqrt\rho\|_1
=\frac{\sqrt{910376791}}{84500},
\qquad
\|\sqrt\rho M_{01}\sqrt\rho\|_1
=\frac{\sqrt{479942241}}{84500}.
$$

$X\rho X=\rho$，而第一历史 $1$ 的两效应是第一历史 $0$ 的效应经过 $X$ 共轭的结果，所以两个第一历史的范数贡献相同。相加得到陈述的协议值。

最后验证严格比较。所有根式均为正，将该协议值与 $\sqrt{949}/25$ 比较，平方并移项后等价于

$$
\sqrt{479942241\cdot910376791}>660059934.
$$

右端为正，再平方可用整数恒等式验证：

$$
479942241\cdot910376791-660059934^2
=1249160754844275>0.
$$

因此这个菜单外的合法协议严格超过菜单内全体协议。原任务的一般连续控制优化仍未完成；本章只排除固定 $\mathsf X/\mathsf Z$ 两轴菜单已经达到原任务最优值这一简化命题。

所用纯化等价与迹范数收缩见 Watrous，*The Theory of Quantum Information*，[Theorem 2.12 与 Corollary 3.40，式 (3.241)](https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf)。引理将这两个标准工具应用到同一个固定历史控制表；菜单上界与菜单外的严格比较由本证明的具体矩阵计算给出。证毕。
<a id="section-50"></a>

## 50. 记录选择与后续预测闭合

**定义 50.1（经典观察的后续闭合）。** 设 $X$ 为有限历史集合，$q:X\to Y$ 为当前读数，$F:X\to X$ 为允许的下一步操作。称 $q$ 对 $F$ 后续闭合，如果存在唯一的映射 $\bar F:q(X)\to q(X)$ 使

$$
q\circ F=\bar F\circ q.
$$

**定理 50.2（有限经典读数的闭合判据）。** 上述 $\bar F$ 存在，当且仅当

$$
q(x)=q(y)\Longrightarrow q(F(x))=q(F(y))
\qquad(x,y\in X).
$$

在存在时，$\bar F(q(x)):=q(F(x))$ 给出唯一的闭合更新。

证明。若 $\bar F$ 存在，对 $q(x)=q(y)$ 代入即可。反之，按右端公式定义 $\bar F$；条件保证它不依赖于代表元，且立即满足 $q\circ F=\bar F\circ q$。证毕。

**定义 50.3（量子记录与一步闭合误差）。** 在同一有限维算符空间上，令 $\mathcal E$ 为幂等的量子记录通道，$\mathcal E^2=\mathcal E$，令 $\Phi$ 为一步量子通道。对密度算符定义迹距离

$$
D(\rho,\sigma)=\frac12\lVert\rho-\sigma\rVert_1,
$$

并定义

$$
\delta(\mathcal E,\Phi)
=\sup_{\rho}D\bigl(\mathcal E\Phi(\rho),\nobreak\mathcal E\Phi\mathcal E(\rho)\bigr),
$$

其中上确界遍历全部密度算符。称记录对一步演化严格闭合，如果

$$
\mathcal E\Phi=\mathcal E\Phi\mathcal E,
$$

等价地，$\mathcal E\Phi(I-\mathcal E)=0$。

**定理 50.4（量子记录的累计预测界）。** 假设记录的像空间由有限个经典记录 $\{P_i\}$ 张成，并且存在经典随机矩阵 $K$ 使

$$
\mathcal E\Phi\mathcal E(\rho)=\iota\!\left(K\,\pi(\rho)\right),
$$

其中 $\pi(\rho)$ 是 $\mathcal E(\rho)$ 在经典记录基下的权重向量，$\iota$ 将权重向量嵌回对角密度算符。令 $A=\mathcal E\Phi$、$B=\mathcal E\Phi\mathcal E$。则对每个密度算符 $\rho$ 及整数 $n\ge0$，

$$
D\bigl(A^n(\rho),B^n(\rho)\bigr)\le n\,\delta(\mathcal E,\Phi).
$$

因此以 $K^n\pi(\rho)$ 预测第 $n$ 步记录时，逐步粗读数分布的误差至多为 $n\delta$。

证明。$A$ 与 $B$ 都是量子通道。望远镜分解与迹距离在量子通道下的收缩性给出

$$
D(A^n\rho,B^n\rho)
\le\sum_{k=0}^{n-1}D\bigl(A(B^k\rho),B(B^k\rho)\bigr)
\le n\delta.
$$

第二个不等式使用 $B^k\rho$ 仍为密度算符。对角记录上的 $B$ 正是 $K$ 的作用，所以其记录权重为 $K^n\pi(\rho)$。证毕。

**定理 50.5（有限维生成元的闭合方向）。** 设 $\Phi_t=e^{t\mathcal L}$ 是有限维、时齐次量子半群，且 $\mathcal E^2=\mathcal E$。则全时严格闭合

$$
\mathcal E\Phi_t=\mathcal E\Phi_t\mathcal E\quad(t\ge0)
$$

当且仅当

$$
\mathcal E\mathcal L(I-\mathcal E)=0.
$$

在 $t\to0$ 时，闭合缺陷满足

$$
\mathcal E\Phi_t(I-\mathcal E)
=t\,\mathcal E\mathcal L(I-\mathcal E)+O(t^2).
$$

条件 $(I-\mathcal E)\mathcal L\mathcal E=0$ 则是 $\mathcal L$ 保持 $\operatorname{Fix}(\mathcal E)$ 的另一方向，不能与前一条件混同。

证明。矩阵指数展开给出后一式。若 $\mathcal E\mathcal L(I-\mathcal E)=0$，则对每个 $m\ge1$ 有 $\mathcal E\mathcal L^m(I-\mathcal E)=0$，因为 $\mathcal E\mathcal L=\mathcal E\mathcal L\mathcal E$，从而指数展开的全部项均为零。反向由对 $t=0$ 的导数得到该条件。对后一方向，若 $X=\mathcal E(Y)$，则 $\mathcal L X\in\operatorname{Fix}(\mathcal E)$ 正是 $(I-\mathcal E)\mathcal L\mathcal E=0$；这描述的是记录像空间的不变性，而不是隐藏部分对未来记录的不可见性。证毕。

**命题 50.6（两种互补记录的共同固定点）。** 对量子比特，令 $\mathcal E_Z$ 与 $\mathcal E_X$ 分别为计算基和 Hadamard 基去相干通道。则

$$
\operatorname{Fix}(\mathcal E_Z)\cap\operatorname{Fix}(\mathcal E_X)=\mathbb C I.
$$

限制到密度算符后，交集只有 $I/2$。

证明。$\mathcal E_Z$ 的固定矩阵为对角矩阵 $\operatorname{diag}(a,b)$。Hadamard 共轭后为

$$
\frac12\begin{pmatrix}a+b&a-b\\a-b&a+b\end{pmatrix}.
$$

它再次对角化当且仅当 $a=b$。归一化迹为一时即得 $I/2$。证毕。

**命题 50.7（受约束编码的动力学检查）。** 设 $P_Z$ 投影到长度 $L$ 的无相邻 $1$ 合法字串空间

$$
\mathcal H_{Z,L}=\operatorname{span}\{|w\rangle:w_jw_{j+1}=0\}.
$$

若 $H$ 是 Hermitian Hamiltonian，则该空间在 $e^{-itH}$ 下无泄漏，当且仅当

$$
[H,P_Z]=0.
$$

因此，仅写出合法 Zeckendorf 叠加并不能保证编码与动力学相容；还须检查这个不变性条件。对一般非 Hermitian 生成元或 Lindblad 通道，必须改用相应的子空间不变性条件，不能直接以该对易式代替。

证明。Hermitian 性使 $P_ZH(I-P_Z)=0$ 与其伴随 $(I-P_Z)HP_Z=0$ 等价；这正是 $H$ 与 $P_Z$ 对易。它又等价于 $e^{-itH}$ 保持 $\operatorname{ran}P_Z$。其余警示是定义域不同的动力学条件。证毕。

**本批来源与边界。** 定理 50.2 是有限集合上的直接因子化证明。量子通道的迹距离收缩、有限维纯化与去相干固定点分别使用本卷既有的通道论证和仓库中的记录模型；其具体闭合判据、累计界、生成元方向区分及 Zeckendorf 子空间检验是本批在这些模型上的推导。本文不把这些命题写成 Lean 已验证结果，也不声称它们给出一般开放系统、无界生成元或全部量子测量的统一定理。对 Lindblad 情形，本批只保留“须另行检查子空间不变性”的边界，不替代该检查。

证毕。

<a id="entry-139"></a>

## 追加锚（新终端）
<a id="section-51"></a>

## 51. 退相干、冗余记录与经典稳定性阈值

**定义 51.1（历史记录模型）。** 设系统 $S$ 的候选经典标签为 $a$，环境分解为

$$
E=E_1\otimes\cdots\otimes E_N,
$$

并取退相干型相互作用

$$
H_{\mathrm{int}}=\sum_a \Pi_a\otimes B_a,
$$

其中 $\{\Pi_a\}$ 是候选指针分解。若初态含有两个标签的相干项 $|a\rangle\langle b|$，在环境演化后其系统系数写成

$$
\rho_{ab}(t)=\rho_{ab}(0)\,\Gamma_{ab}(t).
$$

当环境片段独立耦合时，退相干因子分解为

$$
\Gamma_{ab}(t)=\prod_{k=1}^{N}\gamma_{ab}^{(k)}(t).
$$

**命题 51.2（经典稳定性的候选操作化条件）。** 给定误差容差 $\varepsilon>0$、信息亏损容差 $\delta>0$、形成后时间窗 $[t_{\mathrm{start}},T]$（$0<t_{\mathrm{start}}\le T$）和目标冗余度整数 $R_\ast\ge1$，以下三项构成候选指针记录的操作化条件：

$$
\sup_{t\in[t_{\mathrm{start}},T]}|\Gamma_{ab}(t)|\le\varepsilon
\qquad(a\ne b),
$$

把指针标签 $A$ 视为经典变量，令 $p_a=\operatorname{tr}(\Pi_a\rho)$，并以联合态

$$
\rho_{AF}=\sum_a p_a\,|a\rangle\langle a|\otimes\rho_F^{(a)}
$$

定义互信息；要求存在 $R_\ast$ 个两两不交的环境片段 $F_1,\ldots,F_{R_\ast}\subseteq E$，使得对每个 $j$ 都有

$$
I(A:F_j)\ge(1-\delta)H(A),
$$

以及系统自身 Hamiltonian 满足附加稳定性条件

$$
\|[H_S,\Pi_a]\|\le\eta.
$$

这里最后一个条件只控制系统自身动力学；完整开放动力学还须另行检验相应 Lindblad 生成元对指针代数的近似不变性。因此，本命题把三项作为给定模型和误差阈值下的候选操作化条件，不声称它们是所有量子模型中的普适必要定理。只有再加上完整开放生成元对指针代数的近似不变性，并完成相应动力学验证时，才可在该具体模型内把这些条件作为充分判据。

证明。第一式在形成后窗口内使不同标签之间的局部干涉项低于观测容差；不把 $t=0$ 的初始相干误称为已退相干。第二式表示每个选定环境片段都获得几乎全部指针标签信息；$R_\ast$ 个互不重叠片段同时满足它们，标签便可被独立读取，形成目标冗余记录。第三式限制系统自身动力学在形成后窗口内旋转指针代数的速率；开放系统还需要对其生成元作所述不变性检验。由此，三项分别约束相干性、可复制性和系统内禀稳定性，给出了可执行的候选经典记录判据。该推导只是在指定模型中的条件性结论，并未把“稳定经典现实”提升为无模型的本体定理。证毕。

**定义 51.3（历史冗余度）。** 固定 $\delta$，定义

$$
R_\delta
=
\max\left\{r:\exists\ F_1,\ldots,F_r\ \text{两两不交},\ I(A:F_j)\ge(1-\delta)H(A)\right\}.
$$

在此定义下，“需要多少约束”应改写成：在给定 $\varepsilon,\delta,T$ 和允许的环境分解后，达到

$$
|\Gamma_{ab}|\le\varepsilon,
\qquad
R_\delta\ge R_\ast
$$

所需的最小有效耦合或记录通道数。$R_\ast$ 由任务要求决定，不是量子理论给出的普适常数。

**推论 51.4（历史保留与经典化的条件性关系）。** 若环境保留了区分历史 $a,b$ 的可复制记录，并且命题 51.2 的阈值条件成立，则对只访问系统局部的观测者，相关相干项按 $\Gamma_{ab}$ 衰减，历史差异可作为稳定的经典标签读取；若所有记录都被擦除且系统与环境重新相干，局部干涉在相应可逆操作下原则上可以恢复。

推导。前半句直接由定义 51.1 的退相干因子和命题 51.2 的冗余互信息条件得到：局部观测同时看见小相干项和多个可替代记录。后半句附带“在相应可逆操作下”的条件，因为只有当环境记录及其动力学均可控时，擦除才会恢复相干；单纯忽略环境并不会自动恢复干涉。故这里给出的是操作层面的可检验关系，不是关于单一经典世界的本体断言。来源：退相干与指针稳定性沿用 Zurek，*Rev. Mod. Phys.* **75**, 715 (2003)；互信息与冗余记录沿用 Ollivier、Poulin 与 Zurek，*Phys. Rev. Lett.* **93**, 220401 (2004)。阈值 $\varepsilon,\delta,T,R_\ast$ 是本章的操作化参数，不是上述文献中的普适常数。证毕。
