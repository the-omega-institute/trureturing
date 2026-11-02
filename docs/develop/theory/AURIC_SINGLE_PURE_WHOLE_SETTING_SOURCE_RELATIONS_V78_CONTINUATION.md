# 单一纯整体中的设置—源关系：V78 共同态量词的定量接口

## 1. 对象、类型与继承前提

**定义 1.1（整体、根与所选态）。** 本文区分三种对象。

- $\Omega$ 是包含对象、记录、合法门历史、接口及其相容关系的整体结构。
- $\Omega_0\in H_{\rm tot}$ 是某个有限截口中经校准的单位根向量。
- 本文对用户所称的 $\omega$ 明确选取一种数学类型：有限矩阵代数 $B(H_{\rm tot})$ 上的纯向量态
  $$
  \omega(T)=\langle\Psi,T\Psi\rangle,\qquad \|\Psi\|=1.
  \tag{1.1}
  $$

每个模型固定一个这样的 $\omega$；这不声称所有候选模型只有唯一解。只有在实际门历史 $U$ 已被声明时才写 $\Psi=U\Omega_0$。因此 $\Omega$ 不是向量，$\Omega_0$ 不是态泛函，$\omega$ 也不是允许任意重选的设置参数。两个模型的比较是对同一组假设的两个实现的比较。

全文内积对第二变量线性；密度算符指正半定、迹一的矩阵。

**假设 1.2（继承的关系—量子接口）。** 采用 V78 的共同正核、共同复结构、保尺度二元关系、效果概率、实际后继及复合接口，限制到本问题声明的有限截口。所用接口具体为：

1. 有一个共同有限维复 Hilbert 表示和共同强度标尺；声明的效果采用同一 Born 赋值。
2. 设置记录和源在一个共同的、固定的分解中表示为
   $$
   H_{\rm tot}=H_X\otimes H_Y\otimes H_A\otimes H_B\otimes H_E,
   \quad H_X=H_Y=\mathbb C^2,\quad Q=AB.
   \tag{1.2}
   $$
3. 设置是正交记录 $P_{xy}=|xy\rangle\langle xy|\otimes I_{QE}$，$x,y\in\{0,1\}$。本协议按这些记录分支，后续读出保持它们，不重新干涉不同设置分支。
4. $Q$ 位于读取设置后、执行结果读出前的同一个源切口。凡能返回并影响结果的记忆、参考及辅助均须包含在 $Q$ 及声明的局部接口中。$E$ 在该后续协议中不返回、不控制结果。
5. 两侧结果读出固定为源上的局部二值效果族
   $$
   F^x_a=\frac{I+aA_x}{2},\qquad G^y_b=\frac{I+bB_y}{2},
   \quad a,b\in\{-1,1\},
   \tag{1.3}
   $$
   其中 $A_0,A_1\in B(H_A)$、$B_0,B_1\in B(H_B)$ 是自伴收缩。所有设置依赖均在这些固定的局部读口内；没有另一个未计入的远端设置依赖或选择性筛除。

这些是假设的模型接口。V78 的表示、Born、复合与共同态 CHSH 结果直接复用，不在此重证。张量接口不要求源态在 $A,B$ 之间为乘积；纠缠源完全允许。这里要研究的独立性是整个源 $Q$ 与联合设置 $XY$ 的独立性，类型不同于 $A$ 与 $B$ 之间的独立准备。

若实际读出由声明的局部门历史和终端效果实现，$A_x,B_y$ 就是相应终端读口的 Heisenberg 拉回。V78 的固定根公式同样允许把整个有限历史拉回 $\Omega_0$。此等价不删除门顺序、记录条件或资源前提。

## 2. 实际联合态及其共同源缺陷

**定义 2.1（记录条件下的实际源）。** 对固定的 $\omega$ 定义未归一源块

$$
\sigma_{xy}=\operatorname{Tr}_{XYE}
 \bigl(P_{xy}|\Psi\rangle\langle\Psi|P_{xy}\bigr),
\qquad p_{xy}=\operatorname{Tr}\sigma_{xy}.
\tag{2.1}
$$

假设所有 $p_{xy}>0$，令

$$
\rho_{xy}=\frac{\sigma_{xy}}{p_{xy}},\qquad
\bar\rho=\sum_{xy}p_{xy}\rho_{xy},\qquad
\tau_{XYQ}=\sum_{xy}p_{xy}|xy\rangle\langle xy|\otimes\rho_{xy}.
\tag{2.2}
$$

$\tau$ 是实际设置记录与源的经典—量子联合态，来自同一个 $\omega$。其边缘为

$$
\tau_{XY}=\sum_{xy}p_{xy}|xy\rangle\langle xy|,
\qquad \tau_Q=\bar\rho.
\tag{2.3}
$$

若原始设置程序仍有相干性，式 (2.2) 仅表示本协议按正交记录提取的联合态；不把它替代成所有相干程序操作的全局态。后续若允许跨设置干涉，须恢复相应相干信息。

令

$$
\gamma_{XYQ}=\tau_{XY}\otimes\bar\rho.
\tag{2.4}
$$

$\gamma$ 是保留实际两项边缘的数学比较态；它的存在不表示实际协议能执行一个把 $\tau$ 变成 $\gamma$ 的去相关操作。独立设置边缘 $p_{xy}=p_xp_y$ 不是式 (2.4) 成为实际态的充分条件；下面的定理也不需要设置边缘相互独立。

**定义 2.2（共同源缺陷）。** 对密度算符用半迹范数约定

$$
D(\alpha,\beta)=\frac12\|\alpha-\beta\|_1,
\qquad d_{xy}=D(\rho_{xy},\bar\rho),
\qquad \delta=D(\tau,\gamma).
\tag{2.5}
$$

$\|T\|_1=\operatorname{Tr}\sqrt{T^\dagger T}$。对有限概率表，$\operatorname{TV}(P,P_0)=\frac12\sum_j|P(j)-P_0(j)|$。

$\delta$ 衡量的是实际联合态与其自身边缘乘积的差异，而不是设置频率偏离均匀分布的程度。

**定理 2.3（共同源量词的精确联合形式）。** 对任意满足定义 2.1 的有限模型，

$$
\boxed{\delta=\sum_{xy}p_{xy}d_{xy}.}
\tag{2.6}
$$

以下三项等价：

1. $\delta=0$；
2. 所有设置使用同一个实际源态，即 $\rho_{xy}=\bar\rho$ 对全部 $x,y$ 成立；
3. 对每个 $x,y$ 及源上的每个效果 $0\le T\le I$，
   $$
   \omega\bigl(P_{xy}(I_{XY}\otimes T\otimes I_E)\bigr)
   =p_{xy}\operatorname{Tr}(\bar\rho T).
   \tag{2.7}
   $$

**证明。** $\tau-\gamma$ 在设置记录的四个正交块上分别为 $p_{xy}(\rho_{xy}-\bar\rho)$。正交直和的迹范数是各块迹范数之和，得到 (2.6)。各项非负且 $p_{xy}>0$，故前两项等价。式 (2.7) 左边为 $p_{xy}\operatorname{Tr}(\rho_{xy}T)$。正质量相除后，全部效果的期望相等当且仅当两个 Hermitian 矩阵相等，得到第二、三项的等价。$\square$

式 (2.7) 是实际设置—源的联合约束。V31 §2.2 已给出内部独立性可以成立、但不能仅由共同整体归属推出的警告；本定理给出将该警告接到 V78 共同源量词所需的态级条件。定理没有把这项条件由全局纯性推出。

## 3. 实际联合态上的定量条件定理

**定义 3.1（观察到的条件相关）。** 由实际协议定义

$$
q_{xy}(a,b)=\operatorname{Tr}\bigl(\rho_{xy}F^x_a\otimes G^y_b\bigr),
\qquad E_{xy}=\sum_{a,b}ab\,q_{xy}(a,b)
 =\operatorname{Tr}(\rho_{xy}A_x\otimes B_y),
\tag{3.1}
$$

$$
S_{\rm obs}=E_{00}+E_{01}+E_{10}-E_{11},
\qquad p_{\min}=\min_{xy}p_{xy}>0.
\tag{3.2}
$$

$S_{\rm obs}$ 是四个条件相关的和，通常不是未加权总体输出乘积的期望。特别是设置不均匀时不能把条件相关偷偷换成总体频率。定义没有去掉失败或停止质量；若实际存在这些结果，须先在保留全部质量的二值化中给出本接口，或另行保留更多结果。

令 $c_{00}=c_{01}=c_{10}=1$、$c_{11}=-1$，并把源算符按 (1.2) 扩张，则同一个固定 $\omega$ 上有

$$
S_{\rm obs}=\omega(\mathcal B_p),\qquad
\mathcal B_p=\sum_{xy}\frac{c_{xy}}{p_{xy}}
 P_{xy}(I_{XY}\otimes A_x\otimes B_y\otimes I_E).
\tag{3.2a}
$$

这是带记录条件和逆质量的读口。它不同于通常的 $I_{XY}\otimes S_Q\otimes I_E$，其中 $S_Q=A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1)$。后者在同一个 $\omega$ 中的期望是 $\operatorname{Tr}(\bar\rho S_Q)$，才可直接消费共同态界。因此“全部概率都可写在一个全局态上”并未消除实际条件统计中的设置—源关系。

**定理 3.2（共同源界向实际设置—源态的转移）。** 对假设 1.2 下的每个有限纯整体态、每个满支持设置律及每组固定局部自伴收缩读口，有

$$
\boxed{
 |S_{\rm obs}|
 \le \min\left\{4,\ 2\sqrt2+2\sum_{xy}d_{xy}\right\}
 \le \min\left\{4,\ 2\sqrt2+\frac{2\delta}{p_{\min}}\right\}.
}
\tag{3.3}
$$

更一般地，任取一个共同源密度算符 $\rho_*$，令

$$
S_*=\operatorname{Tr}\rho_*
 \bigl[A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1)\bigr].
\tag{3.4}
$$

则

$$
|S_{\rm obs}-S_*|
 \le 2\sum_{xy}D(\rho_{xy},\rho_*),
\qquad |S_*|\le2\sqrt2.
\tag{3.5}
$$

比较实际联合结果律 $P(xyab)=p_{xy}q_{xy}(a,b)$ 与使用同一设置律、同一读口而以 $\bar\rho$ 为源的律 $P_0$，另有

$$
\operatorname{TV}(P,P_0)\le\delta.
\tag{3.6}
$$

**证明。** 对 Hermitian $H$ 和自伴收缩 $C$，迹范数对偶给

$$
|\operatorname{Tr}(HC)|\le\|H\|_1.
\tag{3.7}
$$

例如把 $H$ 作正、负谱分解并使用 $-I\le C\le I$ 即可得到此式。令 $C_{xy}=A_x\otimes B_y$，其算符范数不超过一。逐项使用 (3.7)，再按 CHSH 的三个正号、一个负号求和，得到 (3.5) 的第一式。第二式直接调用 V78 §12.3 对同一个 $\rho_*$ 的量子界，未将四个不同的 $\rho_{xy}$ 放进共同态证明。

取 $\rho_*=\bar\rho$，三角不等式给 (3.3) 的非代数界。由 (2.6)，

$$
\sum_{xy}d_{xy}
 \le\frac1{p_{\min}}\sum_{xy}p_{xy}d_{xy}
 =\frac\delta{p_{\min}}.
\tag{3.8}
$$

每个 $|E_{xy}|\le1$ 另给代数界四。

对固定设置，实际与比较律应用同一个 POVM。若 $H=\rho_{xy}-\bar\rho$，将正概率差对应的 POVM 效果相加为 $0\le T\le I$，则该设置的总变差为 $\operatorname{Tr}(HT)\le\frac12\|H\|_1=d_{xy}$。按 $p_{xy}$ 加权，并使用 (2.6)，即得 (3.6)。$\square$

**推论 3.3（均匀设置及逆向必要条件）。** 若 $p_{xy}=1/4$，则

$$
|S_{\rm obs}|\le\min\{4,\ 2\sqrt2+8\delta\}.
\tag{3.9}
$$

一般地，令 $t_+=\max\{t,0\}$，有

$$
\delta\ge\frac{p_{\min}}2
 \bigl(|S_{\rm obs}|-2\sqrt2\bigr)_+.
\tag{3.10}
$$

**证明。** 分别代入 $p_{\min}=1/4$，及重排 (3.3)。$\square$

**推论 3.4（共同态的精确消费及其较弱接口）。** $\delta=0$ 足以得到 $|S_{\rm obs}|\le2\sqrt2$。对当前四个相关量，甚至只需

$$
\operatorname{Tr}\bigl[(\rho_{xy}-\bar\rho)C_{xy}\bigr]=0
\quad\text{对每个 }x,y,
\tag{3.11}
$$

而不必已知完整态相等。

**证明。** 式 (3.11) 将四个观察相关同时置换成同一个 $\bar\rho$ 上的相关，随后直接消费 V78 的共同态界。$\delta=0$ 由定理 2.3 蕴含这些等式。$\square$

这些是充分条件。$\delta>0$ 不强制 CHSH 超界；迹距离上界也不从四个局部边缘读数自动取得。由于 $S_{\rm obs}$ 使用条件律，一个很少出现的设置可有很大的条件误差而总体误差很小；式 (3.8) 保留了所需的最小质量。若某个 $p_{xy}=0$，本文不定义该设置的条件源或条件相关，也不以此声称取得四设置结论。

## 4. 一个有限纯整体及完整门读出反例

**定义 4.1（明确声明的有限模型）。** 取八个量子位，按

$$
(X,Y,A,R,L,E_X,E_Y,E_L)
\tag{4.1}
$$

排序。令 $H_A=\mathbb C^2$，$H_B=H_R\otimes H_L$，$Q=ARL$，$E=E_XE_YE_L$。取 $\Omega_0=|0\rangle^{\otimes8}$。仅声明以下门及终端计算基记录：

$$
H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},
\qquad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\tag{4.2}
$$

$$
\operatorname{CX}_{c\to t}|c,t\rangle=|c,t\oplus c\rangle,
\qquad
\operatorname{CCX}_{c,d\to t}|c,d,t\rangle=|c,d,t\oplus cd\rangle.
\tag{4.3}
$$

这里 $Z$ 是计算基结果赋值算符，不需要另行提供一个 $Z$ 门。$H$、CX、CCX 作用在指定的位上，在其余位上取单位。终端计算基读出及其正交记录属于本模型的声明接口；所有 $E$ 位是整体内部的记录，不是外部随机裁判。本定义不把这些门认作某个未说明的 AURIC 原生菜单。

**定理 4.2（同一纯整体内的联合依赖）。** 在定义 4.1 的模型中存在一个有限准备历史和固定有限门读出，使下列五项同时成立。

1. 所选全局态是纯向量态，其单位向量为
   $$
   |\Psi_{\rm dep}\rangle
   =\frac1{2\sqrt2}\sum_{x,y,r\in\{0,1\}}
   |x,y,r,r,x\oplus y,x,y,0\rangle.
   \tag{4.4}
   $$
2. 设置均匀独立，源边缘为
   $$
   p_{xy}=\frac14,\quad
   \bar\rho_Q=\Phi_{AR}\otimes\frac{I_L}{2},\quad
   \Phi_{AR}=|\Phi^+\rangle\langle\Phi^+|,
   \quad |\Phi^+\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2}.
   \tag{4.5}
   $$
   甚至每个单独设置与整个源分别独立：
   $$
   \tau_{XQ}=\frac{I_X}{2}\otimes\bar\rho_Q,
   \qquad \tau_{YQ}=\frac{I_Y}{2}\otimes\bar\rho_Q.
   \tag{4.6}
   $$
3. 在 $A$ 端直接读计算基，在 $B$ 端仅用设置 $Y$ 控制的两个门，所得结果位 $\alpha,\beta$ 满足
   $$
   \Pr(x,y,\alpha,\beta)
   =\begin{cases}
   1/8,&\alpha\oplus\beta=xy,\\
   0,&\alpha\oplus\beta\ne xy.
   \end{cases}
   \tag{4.7}
   $$
   因而每个设置下两端边缘均匀、不信号，而 $S_{\rm obs}=4$。
4. 实际联合设置—源态具有 $\delta=1/2$；其与边缘乘积的区别由一个三方联合记录见证读取，单设置—源边缘不能读取该区别。
5. 另有一个同维数、同根、同门菜单的纯整体模型，它保留 (4.5)、(4.6) 及全部设置边缘，使用完全相同的结果读出，却有 $\delta=0$ 和 $S_{\rm obs}=2$。

**证明。**

先给准备历史。依次对 $X,Y,A$ 施 $H$，施 $\operatorname{CX}_{A\to R}$，再依次施

$$
\operatorname{CX}_{X\to L},\quad
\operatorname{CX}_{Y\to L},\quad
\operatorname{CX}_{X\to E_X},\quad
\operatorname{CX}_{Y\to E_Y}.
\tag{4.8}
$$

$E_L$ 不动。三个 $H$ 和五个 CX 共八门，把 $\Omega_0$ 送到 (4.4)。八个计算基项彼此正交，各振幅为 $1/(2\sqrt2)$，范数平方为一。全局态始终为一条纯向量；设置和源的混合只来自限制到内部子接口。

在 $E_X,E_Y$ 上的互异记录使 $XYQ$ 约化态已经对设置分块。对每个设置，

$$
\rho_{xy}=\Phi_{AR}\otimes|x\oplus y\rangle\langle x\oplus y|_L.
\tag{4.9}
$$

因此 (4.5) 成立。固定 $x$ 后对均匀的 $y$ 求和，奇偶标志 $L$ 恰好各取一次零、一；固定 $y$ 后同理。这证明与整个量子源 $Q$ 的两项乘积等式 (4.6)，并非只证明某个源单比特的均值相同。

结果读出先施

$$
V=\operatorname{CX}_{Y\to R}\operatorname{CCX}_{Y,L\to R},
\tag{4.10}
$$

右侧门先执行，再共同读取 $X,Y,A,R$ 的计算基。$V$ 保持 $X,Y,L$，只改变 $R$。对读取前的位 $(y,r,\lambda)$，其作用为

$$
R_{\rm out}=r\oplus y\lambda\oplus y
 =r\oplus y(1\oplus\lambda).
\tag{4.11}
$$

$A$ 的输出为 $r$。在 (4.9) 的实际分支，$\lambda=x\oplus y$，而二元算术给

$$
y(1\oplus x\oplus y)=xy.
\tag{4.12}
$$

所以两结果位为 $\alpha=r$、$\beta=r\oplus xy$。各 $x,y,r$ 有质量 $1/8$，得到完整律 (4.7)。赋值 $a=(-1)^\alpha$、$b=(-1)^\beta$，读口的源侧表达为

$$
A_0=A_1=Z_A,\qquad
B_0=Z_R\otimes I_L,\qquad B_1=-Z_R\otimes Z_L.
\tag{4.13}
$$

整个读出也可始终保持纯向量：$V|\Psi_{\rm dep}\rangle$ 只是将 (4.4) 中第二个 $r$ 换成 $r\oplus xy$。终端 $X,Y,A,R$ 的计算基投影构成一个共同交换的内部记录代数，其在该纯态上的限制就是 (4.7)。等价地，固定 $\omega_{\rm dep}$，对每个终端记录投影 $\Pi$ 读取 $\omega_{\rm dep}(V^\dagger\Pi V)$；再拉回根则为 $\langle\Omega_0,U_{\rm dep}^\dagger V^\dagger\Pi VU_{\rm dep}\Omega_0\rangle$。这里 $U_{\rm dep}$ 是 (4.8) 连同前面四门的准备历史，不需整体外的读出者。

因此这仍是一组固定的局部二值量子读口。两端都只使用自己的设置；$V$ 不读取 $X$。所用相关量列为

| $xy$ | $\lambda=x\oplus y$ | $E_{xy}$ | CHSH 符号 |
|---|---:|---:|---:|
| $00$ | $0$ | $1$ | $+$ |
| $01$ | $1$ | $1$ | $+$ |
| $10$ | $1$ | $1$ | $+$ |
| $11$ | $0$ | $-1$ | $-$ |

每行两个允许结果对各取 $1/2$，所以两端边缘全为 $1/2$，并给 $S_{\rm obs}=4$。

对同一个固定 $\omega_{\rm dep}$，普通源 Bell 算符却为 $S_Q=2Z_A\otimes Z_R\otimes I_L$，其期望为二；期望为四的是 (3.2a) 的条件读口。因而没有在同一量子态上使通常的 Bell 算符越界。

下面计算联合差异。由 (4.9)，

$$
D(\rho_{xy},\bar\rho)=
 \frac12\left\||x\oplus y\rangle\langle x\oplus y|-I/2\right\|_1
 =\frac12.
\tag{4.14}
$$

故由定理 2.3 得 $\delta=1/2$。可直接再看谱：$\tau-\gamma$ 的每个设置块有两个非零特征值 $+1/8,-1/8$，四块总迹范数为一。联合见证为

$$
W=Z_X\otimes Z_Y\otimes I_{AR}\otimes Z_L,
\qquad \operatorname{Tr}(\tau W)=1,
\qquad \operatorname{Tr}(\gamma W)=0.
\tag{4.15}
$$

$W$ 的范数为一，读取它只需将 $X,Y,L$ 三个计算基记录的符号相乘；不需要源层析。式 (4.6) 已说明所有仅访问 $XQ$ 或仅访问 $YQ$ 的效果都不能区分这两个联合态。区别位于联合记录对与源的关系中。

为给出同边缘对照，取

$$
|\Psi_{\rm ind}\rangle
 =|\Phi^+\rangle_{X E_X}\otimes|\Phi^+\rangle_{Y E_Y}
  \otimes|\Phi^+\rangle_{AR}\otimes|\Phi^+\rangle_{L E_L},
\tag{4.16}
$$

按 (4.1) 的顺序理解张量位。此态用四个 $H$ 和四个 CX 从同一个 $\Omega_0$ 准备：分别在 $X,Y,A,L$ 施 $H$，再分别复制到 $E_X,E_Y,R,E_L$。其 $XYQ$ 约化态恰为

$$
\gamma=\frac{I_{XY}}4\otimes\Phi_{AR}\otimes\frac{I_L}{2}.
\tag{4.17}
$$

两项设置边缘、整个源边缘以及 (4.6) 的两项边缘均与 (4.4) 相同。对照的全局纯化和准备历史不同，这没有要求同一个模型在一次协议中取两种全局态。

对 (4.17) 使用同一 $V$，$\lambda$ 在每个设置内独立均匀。$y=0$ 时 $\beta=\alpha$；$y=1$ 时 $\lambda$ 的平均使 $\alpha,\beta$ 独立均匀。因此

$$
(E_{00},E_{01},E_{10},E_{11})=(1,0,1,0),\qquad S_{\rm obs}=2.
\tag{4.18}
$$

该模型有 $\rho_{xy}=\bar\rho$，故 $\delta=0$。五项全部成立。$\square$

此反例的作用不是再给普通 PR 条件表：该表已经由量子原则卷 §22 给出。这里的承重区别是同一纯整体、明确有限门序列、同一源切口、保边缘比较及其精确 $\delta$。每个条件源都是合法量子态，但它们不共同等于一个源态。准备中的两个设置到标志位的 CX 清楚显示相关性如何写入；此例没有满足独立晚选设置的 Bell 源条件。$S_{\rm obs}=4$ 因而不反驳 V78 的共同态量子界，也不提供超量子资源或物理实现结论。

## 5. 保尺度二元关系和有限三坐标保留了什么

**定义 5.1（二元分解的关系读口）。** 沿用 V78 §5。若内部一个二值端口与其余部分的未归一纯分支写成

$$
|0\rangle\otimes u+|1\rangle\otimes v,
\qquad s=\|u\|^2+\|v\|^2>0,\quad z=\langle u,v\rangle,
\tag{5.1}
$$

则该端口的归一关系表及三坐标为

$$
R(u,v)=\frac1s
 \begin{pmatrix}\|u\|^2&\bar z\\z&\|v\|^2\end{pmatrix}
 =\frac12(I+\mathbf r\cdot\boldsymbol\sigma),
\quad
\mathbf r=\left(\frac{2\operatorname{Re}z}s,
                  \frac{2\operatorname{Im}z}s,
                  \frac{\|u\|^2-\|v\|^2}s\right).
\tag{5.2}
$$

保留 $(s,\mathbf r)$；$s=0$ 单列为零分支，不归一化。V78 的球内性和效果表示直接复用。本节只计算定理 4.2 中的实际对应。

式 (5.2) 的 $\boldsymbol\sigma$ 是数学矩阵基：$\sigma_1=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$、$\sigma_2=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$、$\sigma_3=Z$；列出它们不向原生菜单添加相应操作。

**命题 5.2（相同三坐标边缘不决定共同源）。** 对 (4.4) 和 (4.16)，将 $L$ 作为 (5.1) 的端口，得到下表。表中 $s$ 是相应投影后的整体分支质量，环境向量中保留所有未读的内部记录。

| 保留的设置条件 | 质量 $s$ | 依赖模型中 $L$ 的 $\mathbf r$ | 独立模型中 $L$ 的 $\mathbf r$ |
|---|---:|---|---|
| 无条件 | $1$ | $(0,0,0)$ | $(0,0,0)$ |
| 只保留 $x$ | $1/2$ | $(0,0,0)$ | $(0,0,0)$ |
| 只保留 $y$ | $1/2$ | $(0,0,0)$ | $(0,0,0)$ |
| 同时保留 $x,y$ | $1/4$ | $(0,0,(-1)^{x\oplus y})$ | $(0,0,0)$ |

因此即使保留尺度、源的完整单设置边缘以及设置自身的独立边缘，仍会遗漏定理 4.2 的联合依赖。

**证明。** 无条件的 $L$ 约化表在两模型中均为 $I/2$。在依赖模型中只固定一个设置后，未固定设置及其正交记录使两种奇偶标志各占一半；两环境向量正交，给 $z=0$、等强度。独立模型的 $L E_L$ Bell 对在这些投影下不变，结论相同。

同时固定 $x,y$ 后，依赖模型只有一个 $L$ 基分量非零，强度为 $1/4$；独立模型两个分量强度各为 $1/8$，由 $E_L$ 保持正交。代入 (5.2) 即得四行。$\square$

三坐标的有效性有明确对象：它完整描述这个二元关系表，不自动完整描述 $XYQ$。这里缺失的是设置索引与源标志的配对关系，不是丢失总强度，也不是尚未估准某个单端口虚相干坐标。把联合条件族保留后，缺项已显现在第三坐标的符号中。

此计算不授予全部源效果、任意相位门或三轴层析。例子实际只用计算基记录区分 (4.15)，表中的另两坐标由定义中的已知向量计算。对一般未知原生源，若只能读取有限受限菜单，相同读数只给相应观察商；它不为定义 2.2 的全迹距离提供上界。需要单独的结构证明，或确已声明并证明充分的测试接口。有限三维表示也不把整体 Hilbert 维数或物理空间维数定为三。

## 6. 从内部控制到共同源的一个具体剩余桥梁

**定义 6.1（源切口上的分离控制证书）。** 在设置被写入之前，令 $C$ 包含内部设置种子、控制器、时钟、参考及其可返回记忆，令 $Q$ 包含结果所需的源和局部记忆。取实际联合密度 $\kappa_{CQ}$，定义

$$
\eta=D(\kappa_{CQ},\kappa_C\otimes\kappa_Q).
\tag{6.1}
$$

设理想的分离生成协议为 $\mathcal T_0=\Lambda_C\otimes\Theta_Q$：$\Lambda_C$ 保迹完全正，输出经典设置记录 $XY$；$\Theta_Q$ 保迹完全正，输出同一个 $A,B$ 源接口。设实际完整协议 $\mathcal T$ 也保迹完全正、输出同类型的经典—量子态 $\tau$，并有实际输入上的误差界，$\zeta\ge0$：

$$
D\bigl(\mathcal T(\kappa),\mathcal T_0(\kappa)\bigr)\le\zeta.
\tag{6.2}
$$

协议包括从此前置准备切口到假设 1.2 的共同结果前源切口之间的全部相关设置生成动作；保留全部记录、失败、停止和返回记忆。式 (6.2) 只要求此实际输入，不假定免费取得全 diamond 范数认证。证明一个全输入误差界当然也足够。准备全局态可以仍是纯的；$\kappa$ 只是内部有限接口的约化态。

**定理 6.2（分离证书的定量消费者）。** 在定义 6.1 下，以实际输出的边缘定义 $\delta$，则

$$
\boxed{\delta\le\min\{1,\eta+3\zeta\}.}
\tag{6.3}
$$

若实际、理想协议在 $XY$ 和 $Q$ 上的两个输出边缘精确相同，可改为 $\delta\le\eta+\zeta$。特别地，$\eta=\zeta=0$ 给精确共同源。当实际 $p_{\min}>0$ 且假设 1.2 的读口条件成立时，

$$
|S_{\rm obs}|\le
 \min\left\{4,\ 2\sqrt2+\frac{2(\eta+3\zeta)}{p_{\min}}\right\}.
\tag{6.4}
$$

**证明。** 写

$$
\tau^0=(\Lambda_C\otimes\Theta_Q)(\kappa),\quad
p^0=\Lambda_C(\kappa_C),\quad
\rho^0=\Theta_Q(\kappa_Q).
\tag{6.5}
$$

$p^0,\rho^0$ 正是 $\tau^0$ 的两项边缘。迹距离在保迹完全正映射下收缩，故

$$
D(\tau^0,p^0\otimes\rho^0)\le\eta.
\tag{6.6}
$$

同一收缩性与 (6.2) 给 $D(\tau_{XY},p^0)\le\zeta$、$D(\tau_Q,\rho^0)\le\zeta$。密度算符张量单位质量保持迹范数，配合三角不等式得到

$$
\begin{aligned}
\delta
&\le D(\tau,\tau^0)+D(\tau^0,p^0\otimes\rho^0)
    +D(p^0\otimes\rho^0,\tau_{XY}\otimes\tau_Q)\\
&\le\zeta+\eta+D(p^0,\tau_{XY})+D(\rho^0,\tau_Q)\\
&\le\eta+3\zeta.
\end{aligned}
\tag{6.7}
$$

若边缘相同，最后两项为零。迹距离另不超过一。将 (6.3) 的未截断界代入定理 3.2 即得 (6.4)。所用收缩性是标准迹距离事实：其效果对偶表达在保迹正映射的伴随下仍位于效果区间，故不能增加可区分度。$\square$

**命题 6.3（共同先前记录不能无条件抹去）。** 令有限先前记录 $h$ 由一族正交投影 $R_h$ 给出，$\sum_hR_h=I$，并在后续协议中作为保持的经典记录。置 $w_h=\omega(R_h)$，正质量时定义 $\omega_h(T)=\omega(R_hTR_h)/w_h$；$\tau^h$ 为此条件态按定义 2.1 提取的联合态。若每个正质量 $h$ 上都精确有

$$
\tau^h_{XYQ}=p^h_{XY}\otimes\rho^h_Q,
\tag{6.8}
$$

则共同源结论逐 $h$ 成立，但忽略 $h$ 后不必仍成立。若另有 $p^h_{XY}=p_{XY}$ 对全部正质量 $h$ 相同，则忽略 $h$ 后仍有共同源。

**证明。** 忽略记录得到 $\sum_hw_hp^h\otimes\rho^h$，一般不等于两个边缘的乘积。例如令 $h$ 均匀取零、一，$\rho^h=|h\rangle\langle h|$，并令 $p^0_{00}=1/2$、其他三项各 $1/6$，$p^1_{00}=1/6$、其他三项各 $5/18$。每个条件设置律都有满支持，但在忽略 $h$ 后，源为零的条件概率随设置改变：对 $00$ 为 $3/4$，对其他设置为 $3/8$。若所有 $p^h$ 相同，则直接提取共同因子，得到 $p\otimes\sum_hw_h\rho^h$。$\square$

**定义 6.4（待供应的原生联合独立控制桥）。** 对一个事先固定、真实声明的原生门/读出菜单 $\mathcal N$，要求在相同的源身份、根标定、局部输出、参考及记忆合同下，供应如下对象和结论：

1. 两个内部设置选择程序及共同源准备的实际有限合法历史；在每个所用正质量先前记录 $h$ 上，产生四个正质量联合设置，给定并证明 $p^h_{xy}\ge p_*>0$。
2. 在同一个结果前源切口上，证明 (6.1)、(6.2) 的具体 $\eta_h,\zeta_h$，或直接证明实际联合态的 $\delta_h\le\varepsilon_h$。所有可能返回的控制记忆和参考均在证明范围内，不由名义上的端口分离代替。
3. 证明结果程序确实拉回同一 $A_0,A_1,B_0,B_1$，只有各自局部设置依赖；若结果量还要达到某个非经典值，相关制备与读口也须由该菜单供应。本文的上界本身不要求达到界。
4. 若结论忽略 $h$，证明共同设置律条件或重新计算忽略记录后的实际 $\delta$；不把逐 $h$ 的结论自动平均为无条件独立。

这是一个具体的原生取得义务，尚未由本文的抽象表示条件或例子的扩大门菜单供应。对仅消费四个相关量的目标，第 2 项可减弱到 (3.11)，即证明

$$
\omega_h(P_{xy}C_{xy})
 =p^h_{xy}\,\omega_h(C_{xy})
 \quad\text{对四个 }x,y,
\tag{6.9}
$$

其中 $C_{xy}=A_x\otimes B_y$ 均解释在同一个结果前源切口上。若要完整态级独立，则须保留 (2.7) 的全效果量词。有限四个矩条件比完整态独立弱，不能被报告成后者。

能完成此桥的一种证明，是从该菜单的已校准根和已供应的 ready 资源出发，给出实际合法准备字，证明控制种子—源约化态的乘积或误差界，并沿直到读取设置的全部实际接续证明分离及隔离；随后定理 6.2、3.2 已完成共同源消费者。它不要求执行全源层析。

能反驳某个所提原生充分条件的反模型，须保留该条件所声明的相同菜单、准备、四设置支持、返回记忆和局部读出合同，仍使相应联合等式失败；若条件意在保证 CHSH 界，给出满足全部条件且 $|S|>2\sqrt2$ 的例子即可。若目标是该菜单中独立选择程序的存在性，则须给出对全部许可候选程序的障碍或不变量，单个相关程序的失败不够。定理 4.2 只已反驳“同一纯整体加独立设置边缘，甚至加两个单设置—源独立边缘便足够”这一弱充分条件；它不判定尚未指定的原生菜单能否供应更强程序。

## 7. 文献条件、复用范围与结论边界

**定义 7.1（与测量依赖文献的参数对应）。** Hall 的经典隐藏变量记为 $\lambda$，其条件密度为 $\mu_{xy}(\lambda)$。该文的测量独立性条件是对所有联合设置有 $\mu_{xy}=\mu$，并用

$$
M=\sup_{xy,x'y'}\int
 |\mu_{xy}(\lambda)-\mu_{x'y'}(\lambda)|\,d\lambda
\tag{7.1}
$$

衡量条件分布间的最大全变差的两倍 [H，式 (1)–(4)]。这与本文的量子源态、给定设置先验上的平均量 $\delta$ 有不同对象和量词；本文不把 $\delta$ 称作 Hall 的自由选择百分比。

Pütz 等的测量依赖局域模型是

$$
P(\alpha,\beta,x,y)=\int \mu(d\lambda)
 P(x,y\mid\lambda)
 P(\alpha\mid x,\lambda)P(\beta\mid y,\lambda),
\quad \ell\le P(x,y\mid\lambda)\le h.
\tag{7.2}
$$

他们针对该模型及条件界推导测量依赖局域不等式，并证明对任意严格正的 $\ell$ 存在不能由该模型解释的量子相关 [P，式 (3)–(6) 及其主结论]。它不是“任意部分独立均恢复普通 CHSH 界”的命题，也不是对任意量子源迹距离的定理。

**命题 7.2（有限例子的经典参数核对）。** 仅对定理 4.2 声明的计算基输出，取经典变量 $\lambda_{\rm cl}=(r,l)$。有精确的局域条件表示

$$
\Pr(r,l)=\frac14,\qquad
\Pr(x,y\mid r,l)=\frac12\mathbf1_{\{l=x\oplus y\}},
\quad \alpha=r,\quad \beta=r\oplus y(1\oplus l).
\tag{7.3}
$$

它在 Pütz 等的参数中满足 $\ell=0,h=1/2$，在 Hall 的约定中有 $M=2$，而本文的量子联合缺陷为 $\delta=1/2$。

**证明。** 式 (7.3) 给每个允许的 $(x,y,r,l)$ 质量 $1/8$，正是 (4.7) 的读取前计算基律。相反奇偶设置的 $\lambda_{\rm cl}$ 条件支持不交，故 (7.1) 的距离达到二；(4.14) 已计算 $\delta$。$\square$

此经典表示只适用于已声明读出的概率，不把 Bell 对在所有其他量子效果上的行为改写成非上下文局域答案表。例子有零条件输入格，因此不满足 Pütz 等主结论的严格正下界。V31 的内部独立性警告、普通 PR 表、Hall/Pütz 的测量依赖框架以及 V78 的重建和 Bell 界均为既有供应；本文的推导是这些供应在实际联合设置—源态上的定量条件接合及其有限一纯整体门实现，不作数学优先权主张。

模型前提、数学后果及剩余接口分别为：

| 层次 | 此处的精确内容 |
|---|---|
| 选定模型 | 一个纯向量态 $\omega$；共同有限复表示、Born 效果、固定源切口、局部读口、完整记录。 |
| 条件数学后果 | 联合缺陷恒等式 (2.6)、实际条件 CHSH 界 (3.3)、联合结果稳定性 (3.6)、分离控制转移 (6.3)。 |
| 精确有限反例 | 八位纯态、八门准备和两门结果读出；均匀独立设置、两个单设置—源独立边缘、$\delta=1/2$、$S=4$；同边缘对照的 $\delta=0,S=2$。 |
| 未供应的原生接口 | 定义 6.4 对实际原生菜单的合法取得、源—控制分离界、返回记忆隔离及统一记录量词。 |
| 未作的物理结论 | 纯整体的经验真实性、该门菜单的物理可实现性、设置独立性的实验认证、量子原则的无条件起源。 |

原生独立控制桥是本文留下的具体未决问题。全局共同起源、全局纯性和三坐标关系表与该桥数学上相容，但不蕴含该桥；量子源在两翼之间是否纠缠也不替代该桥。

## 参考来源

**[V78]** AURIC，《内生关系量子论：量子的白话全景与统一关系公理》，固定提交 [b260643d3d496ad9cd04bfc3557fc9b7499de976](https://github.com/the-omega-institute/trureturing/blob/b260643d3d496ad9cd04bfc3557fc9b7499de976/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md)。§§3–9：共同表示、效果、实际后继和独立复合；§5：保尺度二元三坐标；§12.3：共同态 CHSH；§13.2：固定根门序列读出。修订快照 [6b24b302e37ea2ead041655259d42ef4866d3249](https://github.com/the-omega-institute/trureturing/blob/6b24b302e37ea2ead041655259d42ef4866d3249/docs/develop/theory/AURIC_ENDOGENOUS_RELATIONAL_QUANTUM_THEORY_UNIFIED_RELATIONAL_AXIOMS_V78_SYNTHESIS.md) 中后两项分别位于 §15.3、§16.2；共同源消费者相同。

**[V31]** AURIC，《内生记录、长期稳定与时钟几何重建》，[e38cb35074e618f65f662702b8485cbaa47f9789，§2.2](https://github.com/the-omega-institute/trureturing/blob/e38cb35074e618f65f662702b8485cbaa47f9789/docs/develop/theory/AURIC_INTERNAL_RECORDS_LONG_TERM_STABILITY_AND_CLOCK_GEOMETRY_RECONSTRUCTION_V31.md)。内部程序的独立性是具体联合条件，共同整体归属不证明它。

**[QP]** AURIC，《FIB ATOM 与量子基本原则：相干递归的条件综合》，[e38cb35074e618f65f662702b8485cbaa47f9789，§22](https://github.com/the-omega-institute/trureturing/blob/e38cb35074e618f65f662702b8485cbaa47f9789/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)。共同核与经典反事实答案表的区别；归一且不信号的 PR 表并不选出量子。

**[TN]** AURIC，《Triangle Network Source Independence as a Fibered Three-Geometry》，[e38cb35074e618f65f662702b8485cbaa47f9789，§§1、10–11](https://github.com/the-omega-institute/trureturing/blob/e38cb35074e618f65f662702b8485cbaa47f9789/docs/develop/theory/TRIANGLE_NETWORK_SOURCE_INDEPENDENCE_AND_FIBER_GEOMETRY.md)。源独立性是联合约束；其三源网络、熵预算及共同记录问题不直接代入本四设置共同量子源合同。

**[H]** Michael J. W. Hall, “Local Deterministic Model of Singlet State Correlations Based on Relaxing Measurement Independence,” *Physical Review Letters* **105**, 250404. [DOI:10.1103/PhysRevLett.105.250404](https://doi.org/10.1103/PhysRevLett.105.250404)。[arXiv:1007.5518v2](https://arxiv.org/html/1007.5518v2)，题为 “Local deterministic model of singlet state correlations allowing 86% free will”；采用其式 (1)–(4) 的条件分布与 $M$ 约定，不借用其中的最优性或百分比常数。

**[P]** Gilles Pütz, Denis Rosset, Tomer Jack Barnea, Yeong-Cherng Liang, Nicolas Gisin, “Arbitrarily Small Amount of Measurement Independence Is Sufficient to Manifest Quantum Nonlocality,” *Physical Review Letters* **113**, 190402. [DOI:10.1103/PhysRevLett.113.190402](https://doi.org/10.1103/PhysRevLett.113.190402)；[arXiv:1407.5634v2](https://arxiv.org/html/1407.5634v2)，式 (3)–(6) 及主结论。

**[TQI]** John Watrous, *The Theory of Quantum Information*, Cambridge University Press. [作者公开教材](https://cs.uwaterloo.ca/~watrous/TQI/)。迹范数、效果对偶、部分迹和量子通道的标准有限维背景；本文使用的块范数及误差转移已在相应证明中写出。


## 追加锚（本行以下为增补区）
