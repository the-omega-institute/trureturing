# 预测充分性、热力学恢复与隐藏纤维复杂度

> 本卷是 `generic-v1` 理论输入。合入后的正文保持字节不变，勘误与扩充在末尾追加锚之后使用新编号。数学证明身份来自相应 Lean 声明及账本；本文的纸面推导不生成该身份。

## 1. 约定、来源与载体

**约定 1.1（比较的对象）。** 本卷区分三种充分性：给定观测族的未来是否能从当前表示预测；一个状态能否从其边缘与指定热参考恢复；完成这种恢复或配分函数求值需要什么计算资源。经典相空间、有限个正则量子模式及有限维量子子系统分别声明，不用有限维矩阵承担完整的正则交换关系。除指定的观测实验外，动力学参数均已知。

**约定 1.2（符号与单位）。** 所有对数为自然对数，逆温度为 $\beta>0$，有限维量子部分取 $\hbar=1$。密度矩阵熵为 $S(\rho)=-\operatorname{Tr}\rho\log\rho$。相对熵采用支持条件：当 $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$ 时为 $D(\rho\Vert\sigma)=\operatorname{Tr}\rho(\log\rho-\log\sigma)$，否则为 $+\infty$。涉及相对熵相减时均保证两项有限。$\|\cdot\|$ 是欧氏诱导算子范数，$\|\cdot\|_1$ 是迹范数，后者不含二分之一因子。

**出处 1.3（基线与证明范围）。** 本卷承接 PR #8330 的安全版本 `adba22e5f55087c2ce96e30d99cb55a84e8f3c39`，吸收上一轮未入远端的量子与复杂度稿中“隐藏纤维上的恢复与计数”问题，并结合 PR #8891 的 `445d6a7ae62698465e3e63e8fe5d208d29574fa4`。本批新分支基于 `dev@9da8d883041a2a6edabe31e4281e901d30ca60e0`。第 2 节补出辛预测商的热分解；第 3、4 节研究完整量子观测代数、热恢复及隐藏计算；第 5、6 节把时间窗的导数层数连接到全部信息方向和恢复风险。本文不依赖 PR #8891 中一般无界对数的时间窗猜想证明。

## 2. 辛预测商的 Gibbs 分解与热力学恢复

**定义 2.1（正定二次预测商）。** 在 $\mathbb R^{2n}$ 上取标准 $J$、$S=S^{\mathsf T}\succ0$、$A=JS$、$H(z)=z^{\mathsf T}Sz/2$。设 $O\in\mathbb R^{r\times2n}$ 满行秩，$0<r<2n$，且 $OA=KO$。置
\[
 P=OS^{-1}O^{\mathsf T},\qquad
 L=S^{-1}O^{\mathsf T}P^{-1},\qquad N=I-LO.
\]
令 $R$ 的列为 $\ker O$ 的一组欧氏正交基，$C_h=R^{\mathsf T}SR$，$y=Oz$、$u=R^{\mathsf T}Nz$。满行秩和正定性保证 $P,C_h$ 正定。这里 $R$ 表示矩阵，不表示概率参考。

**定理 2.2（同一预测分解同时分离能量、流与热参考）。** 变换 $z=Ly+Ru$ 可逆，且
\[
 H(z)=\tfrac12y^{\mathsf T}P^{-1}y+\tfrac12u^{\mathsf T}C_hu.
\]
动力学分解为 $\dot y=Ky$、$\dot u=A_hu$，其中 $A_h=R^{\mathsf T}AR$。以相空间 Lebesgue 测度定义的 Gibbs 概率 $\pi_\beta\propto e^{-\beta H}$，在此坐标下恰为
\[
 \gamma_r\otimes\gamma_h,
 \qquad\gamma_r=\mathcal N(0,\beta^{-1}P),\quad
 \gamma_h=\mathcal N(0,\beta^{-1}C_h^{-1}).
\]
两因子均由各自的流保持。配分函数满足
\[
 Z_{\rm full}=\kappa Z_rZ_h,\quad
 \kappa=|\det[L\ R]|,\quad
 Z_r=(2\pi/\beta)^{r/2}\sqrt{\det P},\quad
 Z_h=(2\pi/\beta)^{(2n-r)/2}/\sqrt{\det C_h}.
\]

**证明。** $OL=I$、$OR=0$，每个 $z$ 唯一分解成 $LOz+Nz$；$Nz$ 属于 $\ker O$，故坐标变换可逆。由 $L^{\mathsf T}S=P^{-1}O$ 得交叉项 $L^{\mathsf T}SR=0$，以及 $L^{\mathsf T}SL=P^{-1}$，得到能量分解。

由 $AS^{-1}+S^{-1}A^{\mathsf T}=0$ 及 $OA=KO$，有 $KP+PK^{\mathsf T}=0$，继而
\[
 AL=-S^{-1}A^{\mathsf T}O^{\mathsf T}P^{-1}
    =-S^{-1}O^{\mathsf T}K^{\mathsf T}P^{-1}=LK.
\]
所以 $AN=NA$。$\ker O$ 在 $A$ 下不变，因而 $AR=RA_h$，两条自治方程随之成立。常数 Jacobian $\kappa$ 与完成平方给出配分函数及归一化后的乘积分解。最后 $KP+PK^{\mathsf T}=0$ 及 $A_h^{\mathsf T}C_h+C_hA_h=0$ 保证两协方差在各自线性流下不变。这一证明同时保留了非正交坐标变换的测度因子。证毕。[^suff-symplectic]

**定理 2.3（经典自由能的恢复缺陷及其守恒）。** 对 $D(\mu\Vert\pi_\beta)<\infty$ 的概率分布，令 $\nu$ 为其 $y$ 边缘，$\mu(du\mid y)$ 为条件分布，定义恢复 $\mathcal R\nu=\nu\otimes\gamma_h$，再以定义 2.1 的逆变换送回相空间。则
\[
 D(\mu\Vert\pi_\beta)-D(\nu\Vert\gamma_r)
 =\int D(\mu(\cdot\mid y)\Vert\gamma_h)d\nu(y)
 =D(\mu\Vert\mathcal R\nu).
\]
因此给定 $\nu$ 的全部提升中，$\beta^{-1}D(\mu\Vert\pi_\beta)$ 的唯一极小提升是 $\mathcal R\nu$，最小值为 $\beta^{-1}D(\nu\Vert\gamma_r)$。沿完整 Hamilton 流，上述缺陷保持常数。

**证明。** 在定理 2.2 的乘积坐标中分解密度比：
\[
 \log\frac{d\mu}{d(\gamma_r\otimes\gamma_h)}
 =\log\frac{d\nu}{d\gamma_r}
  +\log\frac{d\mu(\cdot\mid y)}{d\gamma_h}.
\]
积分得到链式恒等式；有限总相对熵保证各项有定义。第二个等号对参考 $\nu\otimes\gamma_h$ 使用同一分解。条件 KL 非负且零值要求条件分布相同，故得到唯一极小提升。完整流在两坐标上分别可逆并保持各自热参考，所以总相对熵、边缘相对熵各自不变，其差亦不变。可预测性没有自动使隐藏状态处于条件热平衡，粗粒化也没有自动产生单调熵增长。证毕。

**定理 2.4（正则量子模式上的相容热分解）。** 对定义 2.1 的数据，$r=2k$ 为偶数。有限 $n$ 模 Schrödinger 表示中的 Weyl 对称二次量子 Hamilton 算子，经一个与 $O$ 的预测子空间相容的线性正则变换及其酉实现后，可写为
\[
 \widehat H=\widehat H_r\otimes I+I\otimes\widehat H_h
 \quad\text{于 }L^2(\mathbb R^k)\otimes L^2(\mathbb R^{n-k}).
\]
两块均为正定二次振子，任意 $\beta>0$ 的 Gibbs 算子为迹类，且
\[
 Z_\beta=Z_{r,\beta}Z_{h,\beta},\qquad
 \gamma_\beta=\gamma_{r,\beta}\otimes\gamma_{h,\beta}.
\]
可见 Weyl 代数只作用于第一因子。各块若有模态频率 $\omega_j>0$，其配分函数为 $\prod_j[2\sinh(\beta\hbar\omega_j/2)]^{-1}$。

**证明。** $\operatorname{im}O^{\mathsf T}$ 对 $A^{\mathsf T}$ 不变；若非零 $a$ 是其限制 Poisson 配对的根向量，则
\[
 0=a^{\mathsf T}JA^{\mathsf T}a=(Ja)^{\mathsf T}S(Ja)>0,
\]
矛盾。因此 $J_r=OJO^{\mathsf T}$ 非退化、$r$ 为偶数。由定义 2.1 及前一证明可得 $JO^{\mathsf T}=LJ_r$，从而 $L^{\mathsf T}J=-J_r^{-1}O$。因此 $\operatorname{im}L$ 与 $\ker O$ 辛正交，两者限制辛形式均非退化。分别取 Darboux 基，组成完整线性正则坐标；定理 2.2 的能量交叉项仍为零。

有限模的线性正则变换有 metaplectic 酉实现；Weyl 二次量子化在该变换下协变。这是所引高斯量子理论中的标准构件。它把两个独立坐标块变为两个张量因子，而不会额外产生混合项。各正定块再作 Williamson 对角化，得到能级 $\sum_j\hbar\omega_j(n_j+1/2)$。逐模几何级数收敛并给出所列配分函数，故热态因子化。这里只有限定的模态数，Hilbert 空间仍无限维；一般态的热恢复仍需限制其相关性和隐藏边缘，不能从均值闭合直接认领全态恢复。证毕。[^suff-gaussian]

## 3. 完整量子观测代数的闭合与共同误差证书

**定义 3.1（可见代数与有限泄漏证书）。** 本节取有限维 $\mathcal H_A=\mathbb C^d$、$\mathcal H_B=\mathbb C^e$，$d,e\ge2$，$H=H^\dagger$。令
\[
 h_0=\operatorname{Tr}H/(de),\quad
 H_A=e^{-1}\operatorname{Tr}_BH-h_0I_A,\quad
 H_B=d^{-1}\operatorname{Tr}_AH,
\]
\[
 H_0=H_A\otimes I_B+I_A\otimes H_B,\quad V=H-H_0,
 \quad\mathbb E_A(X)=e^{-1}\operatorname{Tr}_B(X)\otimes I_B.
\]
于是 $\operatorname{Tr}_AV=\operatorname{Tr}_BV=0$。取 $d$ 维 Weyl 单位酉族 $W_{ab}=X^aZ^b$，$0\le a,b<d$，其中 $X|j\rangle=|j+1\bmod d\rangle$、$Z|j\rangle=e^{2\pi ij/d}|j\rangle$。定义
\[
 R_{ab}=(\operatorname{id}-\mathbb E_A)[H,W_{ab}\otimes I],\qquad
 \delta(H)=\max_{a,b}\|R_{ab}\|.
\]
归一化 Hilbert–Schmidt 范数记为 $\|M\|_{2,\mathrm n}^2=\operatorname{Tr}M^\dagger M/(de)$。这些有限矩阵是代数证书，不预设测量它们只需多项式于量子比特数的资源。

**定理 3.2（有限观测泄漏等价于隐藏相互作用）。** 对定义 3.1 有
\[
 R_{ab}=[V,W_{ab}\otimes I],\qquad
 \|V\|\le\delta(H)\le2\|V\|,
\]
以及精确平方恒等式
\[
 \frac1{2d^2}\sum_{a,b}\|R_{ab}\|_{2,\mathrm n}^2
 =\|V\|_{2,\mathrm n}^2.
\]
特别地，$[H,\mathcal B(\mathcal H_A)\otimes I]\subseteq\mathcal B(\mathcal H_A)\otimes I$ 当且仅当 $V=0$，亦当且仅当 $\delta(H)=0$。

**证明。** 条件期望满足双模关系 $\mathbb E_A((M\otimes I)Y)= (M\otimes I)\mathbb E_A(Y)$ 及相应右乘式。由 $\mathbb E_A(V)=0$ 得 $\mathbb E_A[V,W\otimes I]=0$。局部 Hamilton 项的交换子全部在可见代数中，故得到第一式。

在矩阵单位上直接求有限几何和，Weyl 平均满足
\[
 \frac1{d^2}\sum_{a,b}(W_{ab}\otimes I)V(W_{ab}^\dagger\otimes I)
 =d^{-1}I_A\otimes\operatorname{Tr}_AV=0.
\]
因此 $V=d^{-2}\sum_{a,b}R_{ab}(W_{ab}^\dagger\otimes I)$，三角不等式给 $\|V\|\le\delta$。反向用交换子范数界得到 $\delta\le2\|V\|$。展开每个交换子的平方范数，两个平方项各为 $\|V\|_{2,\mathrm n}^2$，交叉项的平均由上述酉平均等式为零，得到平方恒等式。Weyl 矩阵张成完整可见矩阵代数，所以零泄漏与全代数闭合等价；前述界再给 $V=0$。证毕。

**定理 3.3（同一证书控制预测与自由能）。** 令 $U_t=e^{-itH}$、$U_t^0=e^{-itH_0}$。对任意联合态 $\rho$、任意实数 $t$，包括初始相关态，有
\[
 \left\|\operatorname{Tr}_B(U_t\rho U_t^\dagger)
 -e^{-itH_A}\rho_Ae^{itH_A}\right\|_1
 \le\min\{2,2|t|\delta(H)\}.
\]
记 $f_\beta(H)=-\beta^{-1}\log\operatorname{Tr}e^{-\beta H}$、$\gamma_H=e^{-\beta H}/\operatorname{Tr}e^{-\beta H}$、$G_H(\rho)=\beta^{-1}D(\rho\Vert\gamma_H)$。则
\[
 |f_\beta(H)-f_\beta(H_0)|\le\delta(H),\qquad
 |G_H(\rho)-G_{H_0}(\rho)|\le2\delta(H).
\]

**证明。** Duhamel 公式和酉范数为一给 $\|U_t-U_t^0\|\le |t|\|V\|$。插入减去 $U_t^0\rho U_t^\dagger$，迹范数三角不等式给联合态距离至多 $2|t|\|V\|$；偏迹收缩并代入定理 3.2。密度矩阵间迹距离另至多为二。

由 $-\|V\|I\preceq V\preceq\|V\|I$，有序特征值满足 $|\lambda_j(H)-\lambda_j(H_0)|\le\|V\|$。逐特征值取指数求和得两配分函数之比在 $[e^{-\beta\|V\|},e^{\beta\|V\|}]$，从而给出平衡自由能界。最后
\[
 G_H(\rho)=\operatorname{Tr}(\rho H)-\beta^{-1}S(\rho)-f_\beta(H).
\]
两目标之差为 $\operatorname{Tr}(\rho V)-[f_\beta(H)-f_\beta(H_0)]$，绝对值至多 $2\|V\|$。这里使用迹指数的特征值界，不假设一般矩阵指数保持算子序。证毕。

**定理 3.4（热恢复的精确缺陷与扰动界）。** 记 $\gamma_A,\gamma_B$ 为 $H_A,H_B$ 的 Gibbs 态，定义恢复 $\mathcal R(\rho_A)=\rho_A\otimes\gamma_B$。任意联合态均满足
\[
 D(\rho\Vert\gamma_A\otimes\gamma_B)-D(\rho_A\Vert\gamma_A)
 =I(A:B)_\rho+D(\rho_B\Vert\gamma_B)
 =D(\rho\Vert\mathcal R(\rho_A)).
\]
所以零缺陷当且仅当 $\rho=\rho_A\otimes\gamma_B$。若 $V=0$，此缺陷沿全局动力学保持不变。一般 $V$ 下令
\[
 \Delta_H(\rho)=G_H(\rho)-\beta^{-1}D(\rho_A\Vert\gamma_A).
\]
则
\[
 \left|\Delta_H(\rho)-\beta^{-1}D(\rho\Vert\mathcal R(\rho_A))\right|
 \le2\delta(H),
\]
\[
 \|\rho-\mathcal R(\rho_A)\|_1
 \le\min\left\{2,\sqrt{2\beta\,[\Delta_H(\rho)+2\delta(H)]}\right\}.
\]
$\Delta_H$ 使用指定局部 Gibbs 参考；$V\ne0$ 时它本身不被断言为非负的数据处理缺陷。

**证明。** 用 $\log(\sigma\otimes\tau)=\log\sigma\otimes I+I\otimes\log\tau$ 展开相对熵，得到前两个等式。对于可能奇异的 $\rho_A$，正性保证 $\operatorname{supp}\rho\subseteq\operatorname{supp}\rho_A\otimes\mathcal H_B$，故最后一个相对熵仍有限：若 $v\in\ker\rho_A$，正算子的各个 $\langle v\otimes b,\rho(v\otimes b)\rangle$ 非负且总和为零，因此整个相应子空间被 $\rho$ 消去。于是可以在支持上展开对数。

相对熵非负且仅在同态时为零，得到恢复刻画。$V=0$ 时演化为两个局部酉的张量积，各自保持 Gibbs 参考、边缘熵及联合熵，故缺陷守恒。一般情形将定理 3.3 的 $G$ 界代入恒等式即得第一条误差界。最后使用自然对数约定下的量子 Pinsker 界 $\|\rho-\sigma\|_1^2\le2D(\rho\Vert\sigma)$。该界可由相对熵的数据处理、投影到 $\rho-\sigma$ 的正谱空间以及二元经典 Pinsker 推出；结合第一条界得到结论，并保证根号内非负。证毕。[^suff-dpi]

**命题 3.5（少量观测闭合不推出热解耦）。** 取两个量子比特，$H=Z\otimes Z$。可见线性观测空间 $\operatorname{span}\{I,Z\}\otimes I$ 完全闭合，但 $V\ne0$、$\delta(H)=2$；存在相同初始可见边缘，其后续可见边缘不同。热态在任何 $\beta>0$ 都不分解为两个边缘的乘积。

**证明。** $[H,Z\otimes I]=0$。定义 3.1 给 $H_A=H_B=0$、$V=H$，取 Weyl 矩阵 $X$ 得 $\|[Z\otimes Z,X\otimes I]\|=2$，且定理 3.2 给反向上界。初态 $|+\rangle\langle+|\otimes|0\rangle\langle0|$ 与 $|+\rangle\langle+|\otimes|1\rangle\langle1|$ 的可见边缘相同，之后分别按 $e^{-itZ}$ 和 $e^{itZ}$ 旋转。在 $t=\pi/4$，两者的 Pauli $Y$ 期望值为 $1$ 和 $-1$；其 $Z$ 读数却一直相同。另有
\[
 \gamma_H=\tfrac14(I-\tanh\beta\,Z\otimes Z),\qquad
 (\gamma_H)_A=(\gamma_H)_B=I/2.
\]
因此联合态不等于边缘乘积。此例说明不变线性观测空间与完整局部算子代数是不同前件。证毕。

## 4. 完美预测下的热信息缺口与计数复杂度

**定义 4.1（只访问可见子系统）。** 一个可见实验可以使用任意有限次数的联合动力学等待和仅作用于 $A$ 的量子仪器，可按此前结果选择后续仪器及等待时间。仪器的 Kraus 算子均形如 $M\otimes I_B$。实验只返回 $A$ 的经典记录，没有隐藏能量或隐藏态的额外预言机。

**定理 4.2（无相互作用时仍有精确的热量辨识下界）。** 设 $H=H_A\otimes I_B$、$\dim\mathcal H_B=e\ge2$，固定可见初态 $\rho_A$，隐藏初态 $\sigma_B$ 任意。所有定义 4.1 实验的记录分布与 $\sigma_B$ 无关。若目标为隐藏的超额自由能
\[
 \theta(\sigma_B)=\beta^{-1}D(\sigma_B\Vert I/e)
 =\beta^{-1}(\log e-S(\sigma_B)),
\]
则允许任意这些实验和任意随机估计器，其最坏期望绝对误差的最小值恰为 $\log e/(2\beta)$。

**证明。** 每个产品初态经等待后仍为产品态，可见因子独立演化；任一可见仪器的分支概率及更新只作用于第一因子。按实验记录长度归纳，包括自适应分支选择，全部记录分布与隐藏因子无关。特别地，隐藏纯态与 $I/e$ 产生相同数据，其目标值分别是 $L=\log e/\beta$ 与零。对同一随机估计值 $Z$，有 $\mathbb E|Z|+\mathbb E|Z-L|\ge L$，故最坏风险至少为 $L/2$。恒输出 $L/2$ 对全部 $0\le\theta\le L$ 达到上界。这是观测限制下的辨识结论，尚未限制算法运行时间。证毕。

**定理 4.3（零泄漏可见系统中的单次配分函数计数归约）。** 给定 $n$ 个变量、$m$ 个至多三文字子句的 CNF 公式 $F$，可在多项式时间内构造对角、相互对易、至多三局域的隐藏 Hamilton 算子 $H_F$，并增加一个与其解耦的可见量子比特，使可见观测代数泄漏严格为零，而在固定 $\beta=\log2$ 下，完整配分函数的一次精确有理数求值即可恢复 $\#\mathrm{SAT}(F)$。

**证明。** 对每个子句取其被违反的计算基赋值投影 $\Pi_j$，并令
\[
 H_F=(n+1)\sum_{j=1}^m\Pi_j,\qquad
 H=|1\rangle\langle1|_A\otimes I+I_A\otimes H_F.
\]
子句投影对角且支撑至多三个变量；系数 $n+1$ 可二进制编码，也可用多项式个相同单位范数项替代。令 $N_k$ 为恰违反 $k$ 个子句的赋值数，则
\[
 Z_F=\sum_{k=0}^mN_k2^{-(n+1)k},\qquad
 0\le Z_F-N_0\le2^n2^{-(n+1)}=1/2.
\]
可见配分函数为 $3/2$，所以
\[
 \boxed{\#\mathrm{SAT}(F)=\left\lfloor\tfrac23 Z_H\right\rfloor.}
\]
输出有公共分母 $2^{(n+1)m+1}$，其分子、分母的位数为输入规模的多项式。$H$ 解耦，故定理 3.2 给出零泄漏和精确的全部可见预测；但其总配分函数仍携带计数问题。

因此该精确求值任务至少具有 $\#3\mathrm{SAT}$ 的计数难度。对状态族 $\rho_A\otimes\gamma_{H_F}$，定理 3.4 的恢复缺陷也严格为零；这一数学恢复公式没有提供高效生成隐藏 Gibbs 态的算法。该归约没有强加固定几何格点、固定每点总相互作用强度或一维衰减前件，也没有证明固定误差的自由能近似同样困难。它不属于第 2 节可由 Gaussian 行列式求值的正定二次族。证毕。[^suff-count]

## 5. 导数分层决定全部短窗信息尺度

**定义 5.1（有限维导数层与观测 Gramian）。** 设 $B\in\mathbb R^{d\times d}$、$C\in\mathbb R^{p\times d}$，$d,p\ge1$，且 $(C,B)$ 可观测。令
\[
 V_0=\mathbb R^d,\quad V_j=\bigcap_{k=0}^{j-1}\ker(CB^k),\quad
 m=\min\{j:V_{j+1}=\{0\}\},
\]
\[
 E_j=V_j\cap V_{j+1}^{\perp},\quad d_j=\dim E_j,
 \quad\mathbb R^d=\bigoplus_{j=0}^m E_j.
\]
定义 $D_T|_{E_j}=T^{j+1/2}I$，以及
\[
 G(T)=\int_0^T e^{tB^{\mathsf T}}C^{\mathsf T}Ce^{tB}dt,
 \qquad\mathfrak q=\sum_{j=0}^m(2j+1)d_j.
\]
所有短窗极限都在固定矩阵、固定欧氏范数及已固定时间单位下令 $T\downarrow0$。$\mathfrak q$ 是本节行列式缩放指数，不是量子比特数。

**定理 5.2（分层极限矩阵、全谱幂次与行列式首项）。** 对 $x=\sum_jx_j$、$x_j\in E_j$，定义
\[
 \mathcal P(s)x=\sum_{j=0}^m\frac{s^j}{j!}CB^jx_j,
 \qquad M=\int_0^1\mathcal P(s)^{\mathsf T}\mathcal P(s)ds.
\]
则 $M\succ0$，并在算子范数下有
\[
 D_T^{-1}G(T)D_T^{-1}=M+O(T).
\]
因此存在固定 $a,b,T_*>0$ 使
\[
 aD_T^2\preceq G(T)\preceq bD_T^2\quad(0<T<T_*),
\]
每个层 $j$ 对应 $d_j$ 个按大小排序的特征值 $\Theta(T^{2j+1})$，且
\[
 \boxed{\det G(T)=T^{\mathfrak q}(\det M+O(T)).}
\]

**证明。** 对 $x_j\in E_j\subset V_j$，$CB^kx_j=0$ 对 $k<j$ 成立。矩阵指数的 Taylor 余项在 $s\in[0,1]$ 上一致受控，因此
\[
 \sqrt T\,Ce^{TsB}D_T^{-1}x
 =\sum_j\sum_{k\ge j}\frac{T^{k-j}s^k}{k!}CB^kx_j
 =\mathcal P(s)x+O(T)\|x\|.
\]
平方积分便得到极限矩阵。若 $x^{\mathsf T}Mx=0$，连续非负被积函数为零，故向量多项式 $\mathcal P(s)x$ 的每个系数都为零。于是 $CB^jx_j=0$；结合 $x_j\in V_j$ 得 $x_j\in V_{j+1}$，又因 $x_j\perp V_{j+1}$ 得 $x_j=0$，因此 $M$ 正定。

对足够小 $T$，极限矩阵的正特征值从上下控制缩放后的 Gramian。合同变换给出 Loewner 夹逼；Courant–Fischer 原理将该夹逼逐项转成排序特征值界。最后 $\det D_T^2=T^{\mathfrak q}$，行列式在 $M$ 附近连续可微，得到首项公式。整个谱的幂次与经典可控 Gramian 结果对偶，本卷不认领该幂次的首创；这里显式保留分层极限矩阵，供后续统计信息计算。证毕。[^suff-gramian]

**定理 5.3（有限正交积分矩保留整个分层首项）。** 取 $L^2(0,1)$ 中次数至多 $m$ 的正交归一多项式 $\ell_0,\ldots,\ell_m$。令
\[
 (\mathcal M_Tx)_k=T^{-1/2}\int_0^T\ell_k(t/T)Ce^{tB}x\,dt,
 \qquad G_{\rm mom}(T)=\mathcal M_T^{\mathsf T}\mathcal M_T.
\]
则
\[
 D_T^{-1}G_{\rm mom}(T)D_T^{-1}=M+O(T).
\]
因此定理 5.2 的全部幂次和行列式首项也由这 $(m+1)p$ 个标量积分矩实现。对应积分映射对 $L^2$ 扰动为收缩映射。

**证明。** 用 $t=Ts$ 把轨迹等距送到 $L^2(0,1;\mathbb R^p)$。这些积分矩就是到次数至多 $m$ 的向量多项式子空间的正交投影。定理 5.2 中的极限 $\mathcal P(s)x$ 已在该子空间内；投影保持极限，同时把 $O(T)$ 余项范数至多缩小。再取 Gramian 即得结论。扰动收缩是正交投影的范数性质。此处没有对带噪数据作高阶差分，也没有把离散求积误差设为零。证毕。[^suff-window]

## 6. 热先验下的信息获取与噪声分层

**定义 6.1（有限 Gaussian 观测实验）。** 在定义 5.1 的系统中，$X\sim\mathcal N(0,\beta^{-1}I_d)$。从轨迹映射 $x\mapsto Ce^{tB}x$ 的 $d$ 维像中取正交归一基，测其积分坐标。相应矩阵 $M_T$ 满足 $M_T^{\mathsf T}M_T=G(T)$。数据为
\[
 Y_T=M_TX+\sigma\xi,\qquad\xi\sim\mathcal N(0,I_d),\quad\xi\perp X,
\]
其中 $\sigma^2>0$ 是每个归一积分坐标的噪声方差。也可使用定理 5.3 的有限积分矩、独立等方差噪声和 $G_{\rm mom}$。这是有限维经典统计实验，没有把白噪声当作普通 $L^2$ 随机函数，也没有假定对不对易量子观测可以无扰动地连续测量。

**定理 6.2（信息、Bayes 能量风险与条件自由能）。** 在定义 6.1 下，后验为 Gaussian，其协方差和均值是
\[
 \Sigma_T=(\beta I+\sigma^{-2}G(T))^{-1},\qquad
 \widehat X=\sigma^{-2}\Sigma_TM_T^{\mathsf T}Y_T.
\]
互信息和最小平均二次能量误差分别为
\[
 I_T=I(X:Y_T)=\tfrac12\log\det(I+G(T)/(\beta\sigma^2)),
\]
\[
 \mathcal R_T=\inf_{\widehat x}\mathbb E\tfrac12\|X-\widehat x(Y_T)\|^2
             =\tfrac12\operatorname{Tr}\Sigma_T.
\]
对概率密度定义 $\mathcal F(p)=\mathbb E_p\|X\|^2/2-\beta^{-1}h(p)$，则
\[
 \mathbb E_{Y_T}[\mathcal F(p_{X|Y_T})-\mathcal F(p_X)]=\beta^{-1}I_T.
\]
若另有 $B^{\mathsf T}=-B$，估计器 $e^{tB}\widehat X$ 在任意未来 $t\ge0$ 的最小平均二次误差仍为 $\mathcal R_T$。

**证明。** 把先验和似然的二次指数相乘，完成平方得到后验均值与协方差。条件期望在平方损失下最优，故风险为后验协方差迹的一半。Gaussian 熵公式给
\[
 I_T=\tfrac12\log\det(\beta^{-1}I)-\tfrac12\log\det\Sigma_T,
\]
整理得所述行列式。平均条件能量等于先验能量，而 $h(X)-h(X|Y_T)=I_T$，因此条件自由能式成立。它衡量条件概率描述的自由能泛函，未指定实际测量、反馈或擦除协议，不能直接解释为已经付出的热量。最后反对称生成元的流正交，平方误差在该流下保持，且条件期望随已知线性映射交换，得到全部未来的同一 Bayes 风险。未知生成元的辨识误差不包含在此结论中。证毕。[^suff-information]

**定理 6.3（噪声指数选择可恢复的导数层）。** 在定义 6.1 中固定 $\beta$，令 $\sigma^2=T^\alpha$，$\alpha\in\mathbb R$。则
\[
 \boxed{I_T=\frac12\sum_{j=0}^m d_j(\alpha-2j-1)_+\log(1/T)+O(1).}
\]
若 $\alpha$ 不等于任何有 $d_j>0$ 的阈值 $2j+1$，则
\[
 \boxed{\lim_{T\downarrow0}\mathcal R_T
 =\frac1{2\beta}\sum_{2j+1>\alpha}d_j.}
\]
对任意正噪声日程 $\sigma^2(T)$，全部状态的 Bayes 均方误差趋零，当且仅当 $\sigma^2(T)=o(T^{2m+1})$。若 $\sigma^2$ 固定，则
\[
 I_T=\frac{T}{2\beta\sigma^2}\operatorname{Tr}(C^{\mathsf T}C)+O(T^2).
\]

**证明。** 定理 5.2 将 Gramian 特征值按层写成 $\lambda_i(T)=\Theta(T^{2j+1})$。代入定理 6.2 的 $\log(1+\lambda_i/(\beta T^\alpha))$：$\alpha>2j+1$ 时贡献 $(\alpha-2j-1)\log(1/T)+O(1)$；相等时有界；小于时趋零。各项求和得到第一式。

后验的对应特征值为 $(\beta+T^{-\alpha}\lambda_i(T))^{-1}$，在严格大于阈值时趋零，在严格小于时趋于 $1/\beta$，得到第二式。有限维下风险趋零等价于最大后验特征值趋零，也就是 $\lambda_{\min}(G(T))/\sigma^2(T)\to\infty$；用 $\lambda_{\min}(G(T))=\Theta(T^{2m+1})$ 得充要条件。固定噪声时 $G(T)=TC^{\mathsf T}C+O(T^2)$，对 $\log\det(I+M)$ 作零点展开得到最后一式。这个首阶互信息只能读取初始观测增益，不能单独认证高阶隐藏方向的恢复。证毕。

**定理 6.4（同一双振子的等增益传感器有不同信息与恢复极限）。** 在能量归一坐标 $(q_1,p_1,q_2,p_2)$ 中取
\[
 B=\operatorname{diag}(J_2,2J_2),\quad J_2=\begin{pmatrix}0&1\\-1&0\end{pmatrix},
\]
\[
 C_{\rm sum}=(1,0,1,0),\qquad
 C_{\rm sep}=\begin{pmatrix}1&0&0&0\\0&0&1&0\end{pmatrix}.
\]
二者均满足 $\operatorname{Tr}C^{\mathsf T}C=2$，但其分层与 Gramian 行列式为
\[
 (d_0,d_1,d_2,d_3)_{\rm sum}=(1,1,1,1),\quad
 \det G_{\rm sum}(T)\sim T^{16}/2688000,
\]
\[
 (d_0,d_1)_{\rm sep}=(2,2),\qquad
 \det G_{\rm sep}(T)\sim T^8/36.
\]
当每个归一积分坐标的噪声方差为 $T^4$ 时，
\[
 I_{\rm sum}(T)=2\log(1/T)+O(1),\quad
 I_{\rm sep}(T)=4\log(1/T)+O(1),
\]
\[
 \mathcal R_{\rm sum}(T)\longrightarrow\beta^{-1},\qquad
 \mathcal R_{\rm sep}(T)\longrightarrow0.
\]
固定相同噪声方差时，两者的互信息首项却相同，均为 $T/(\beta\sigma^2)$。

**证明。** 合成位置的导数矩阵逐层秩为 $1,2,3,4$；分别测位置时为 $2,4$。合成位置取行矩阵 $V$ 的第 $k$ 行为 $CB^k/k!$，$k=0,1,2,3$，直接计算
\[
 \det V=3/2,\qquad \det(1/(i+j+1))_{i,j=0}^3=1/6048000.
\]
Taylor 首项给 $\det G_{\rm sum}(T)\sim T^{16}(\det V)^2\det H_3=T^{16}/2688000$。分别测位置的 Gramian 为两个独立模态块，频率 $\omega$ 的块行列式为
\[
 \tfrac14\left(T^2-\frac{\sin^2(\omega T)}{\omega^2}\right)
 \sim\omega^2T^4/12.
\]
取 $\omega=1,2$ 相乘得到 $T^8/36$。其余各式代入定理 6.3；在噪声指数四时，合成读数仍有第五、第七幂两个信息方向没有被恢复，分别测位置的第一、第三幂方向均被恢复。能量归一坐标可取 Poisson 矩阵 $\operatorname{diag}(J_2,2J_2)$、能量 $\|x\|^2/2$；它是正定双振子的常数坐标变换，未把欧氏先验与另一套未归一能量混用。证毕。[^suff-window]

## 7. 来源分层、限定条件与证明身份

**出处 7.1（仓库推导的接口）。** 第 2 节使用 PR #8891 中预测行空间、最小能量提升及辛配对的矩阵对象，补出热参考分解和可恢复条件；其证明已在本卷完整展开。第 3、4 节吸收上一稿的相对熵逃逸与 witness 纤维问题，但收紧到完整子系统代数和明确的精确求值任务。第 5 节把 PR #8891 的最坏时间窗下界细化为全部导数层。第 6 节将这些层代入明确的有限 Gaussian 实验。一般正规算子的时间窗猜想、相对论、一般场论及四种物理理论的无条件等价均不是本卷结论。

**出处 7.2（既有定理与本批计算）。** Gibbs/KL 分解、线性正则量子化、量子 Pinsker、Gaussian 后验及 Gramian 小时间谱幂次属于已有数学，本卷将其列为 `literature-attested` 构件。本卷的共同泄漏证书、相容热恢复链、隐藏热风险实例、固定温度单次计数归约、噪声阈值组合和双振子常数按所给证明列为 `repo-derived`。这说明推导来源，不确立全球首创；本卷不新增任何为包装既有命题而生成的 Lean 声明。

[^suff-symplectic]: 固定 PR #8891 源卷：[SYMPLECTIC_PREDICTIVE_COMPLETION.md](https://github.com/the-omega-institute/trureturing/blob/445d6a7ae62698465e3e63e8fe5d208d29574fa4/docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md)，第 4 至 7 节。它给出正定二次系统的最小预测商、辛非退化性及最小能量提升；本卷补出测度因子、热状态及条件相对熵，未用该引用代替新增证明。

[^suff-gaussian]: Christian Weedbrook 等，*Gaussian Quantum Information*，Reviews of Modern Physics 84, 621–669 (2012)，[作者预印本 arXiv:1110.3234](https://arxiv.org/abs/1110.3234)。核对其 II.C.1、II.C.2 的 Williamson 分解、正则酉与张量热分解。Guofeng Zhang、Jinghao Li、Zhiyuan Dong、Ian R. Petersen，*The Quantum Kalman Decomposition: A Gramian Matrix Approach*，[arXiv:2312.16082v1](https://arxiv.org/html/2312.16082v1)，是量子可观测分解的背景。本文第 2.4 条固定有限模、Schrödinger 表示及 Weyl 二次量子化；第 3 节另用有限维子系统矩阵。

[^suff-dpi]: Alexander Müller-Hermes、David Reeb，*Monotonicity of the Quantum Relative Entropy Under Positive Maps*，[arXiv:1512.06117](https://arxiv.org/abs/1512.06117)。使用相对熵在测量下的数据处理作为量子 Pinsker 的经典前置。仓库已有 `QuantumRelativeEntropyDefectComposition` 的代数相加律和 `CoherentCopyCorrelationTax` 的具体相关性身份；代数相加本身不证明一般非负性，本卷不据文件名冒领该义务的机器闭合。

[^suff-count]: A. García-Sáez、J. I. Latorre，*An exact tensor network for the 3SAT problem*，[arXiv:1105.3201](https://arxiv.org/abs/1105.3201)，给出量子态范数计数与 $\#P$ 的既有背景。本文第 4.3 条使用另行写出的对角 Hamilton 构造，并区分精确配分函数与定精度近似。Haimeng Zhao、Yuzhen Zhang、John Preskill，*Learning to erase quantum states: thermodynamic implications of quantum learning theory*，[arXiv:2504.07341v2](https://arxiv.org/html/2504.07341v2)，在其密码学前件下区分最优擦除功与高效可达性；本卷没有把其假设替换为 P 与 NP 的已证分离。

[^suff-gramian]: Edward Schmerling、Lucas Janson、Marco Pavone，*Optimal Sampling-Based Motion Planning under Differential Constraints: the Drift Case with Linear Affine Dynamics*，CDC 2015，2574–2581，DOI [10.1109/CDC.2015.7402604](https://doi.org/10.1109/CDC.2015.7402604)。核对[作者全文](https://pmc.ncbi.nlm.nih.gov/articles/PMC4795843/)第 III.B 节 Lemma III.1、III.4，已给可控 Gramian 的分层谱幂次与行列式阶。本卷采用其可观测对偶的完整缩放矩阵证明，新增组合不被表述为首次发现 Gramian 幂次。

[^suff-window]: 固定 PR #8891 源卷：[PREDICTIVE_OBSERVABILITY_TIME_WINDOWS.md](https://github.com/the-omega-institute/trureturing/blob/445d6a7ae62698465e3e63e8fe5d208d29574fa4/docs/develop/theory/PREDICTIVE_OBSERVABILITY_TIME_WINDOWS.md)，第 4、7、8 节。原卷最坏噪声误差由最小 Gramian 特征值控制；本文使用整个分层谱计算随机实验的互信息、Bayes 风险和行列式常数，保留两种噪声模型的区别。

[^suff-information]: Yuksel Subasi、Mubeccel Demirekler，*Quantitative measure of observability for linear stochastic systems*，Automatica 50(6), 1669–1674 (2014)，DOI [10.1016/j.automatica.2014.04.008](https://doi.org/10.1016/j.automatica.2014.04.008)，已研究以互信息衡量线性 Gaussian 系统可观测性。Sara Pérez-Vieites、Sahel Iqbal、Simo Särkkä、Dominik Baumann，*Online Bayesian Experimental Design for Partially Observed Dynamical Systems*，[arXiv:2511.04403v1](https://arxiv.org/abs/2511.04403v1)，研究部分观测下的信息增益设计。本文第 6 节是固定线性生成元、有限归一积分读数的精确统计推导，没有运行该文算法。

**出处 7.3（与有效热恢复前沿的交界）。** Samuel O. Scalet 等，*Classical Estimation of the Free Energy and Quantum Gibbs Sampling from the Markov Entropy Decomposition*，[arXiv:2504.17405v1](https://arxiv.org/html/2504.17405v1)，Theorem 1、2 使用有效相互作用衰减、局部边缘近似及恢复映射，分别建立自由能近似和全局 Gibbs 制备保证。这些是正向算法的额外前件。本卷第 4.3 条只给一个全局二分下的零泄漏；它没有提供该文所需的全部空间分区衰减或边缘求值能力，因此没有否定那些算法。

**约定 7.4（本批产地与核验）。** 本批采用仓库 `theory-volume-template` 新卷结构。数学推导、来源核对、文字实施及精确代数/数值检错由本会话 ChatGPT 单席串行完成，没有独立模型或同行审定。十四条结果均为纸面证明。未新增 Lean、Scribe、冻结或消化结算状态，未运行 Lean kernel、canonical `make ingest` 或仓库 CI。有限矩阵、数值积分和小公式计数只用于检错，不能替代全部维数、全部态和渐近量词的证明。正文与已有卷分置，使原卷字节与其他并行 PR 不受本次写入影响。

## 追加锚（本行以下为增补区）
