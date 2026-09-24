# 热校准与动力学恢复

## 1. 定位、范围与来源

本卷研究一个有限维两标签恢复问题：同一个完全正、迹保持映射既恢复给定的条件热态，又尽可能保存可见相干，并与指定的输入、输出 Hamilton 动力学精确或近似相容。概率校准、态族恢复、时间协变与热操作的物理可实现性是不同条件；下文不从前三者推出无功代价的热浴实现。

已有干涉理论给出无动力学约束时的两态根保真度上限 [OA06]；对称量子动力学给出频率模态选择规则 [MS14]；热操作文献说明 Gibbs 保持与时间协变均不足以单独刻画有相干的能量守恒实现 [LJR15, FOR15]。这些结果只作为下文推导的中间输入。引理 2.2 的指定恢复类参数化、定理 3.1 的非对易谱块最优式、推论 3.2 的热谱交集式、定理 4.2 的完全可区分误差恒等式与定理 4.3 的有限时间精确前沿在本卷中直接推导；这里不主张文献优先权。

多元保真度的正块半定规划与操作解释问题提供多标签背景 [NMLW25]。本卷只处理两个标签，不解决一般多标签的共同正块与环路相容性。统计推断下的尺度描述提示应区分信息损失与动力学交织误差 [BO15]；标准通道复合三角界与相对熵 telescoping 只作为背景，不列为本卷的新命题。

## 2. 热校准恢复中的状态、概率与共同动力学

**定义 2.1（正归一状态与热恢复实验）。** 在有限维经典模型中，一个状态是交换代数上的正归一线性泛函；在有限维量子模型中，写为 $a\mapsto\operatorname{Tr}(\rho a)$，其中 $\rho\succeq0$、$\operatorname{Tr}\rho=1$。效应 $0\preceq E\preceq I$ 的概率为 $\operatorname{Tr}(\rho E)$。经典对角子代数给出普通概率向量，但不删除量子代数的非对易乘法或复合规则。量子变换以下均为完全正、迹保持映射，记为 CPTP。

固定隐藏空间 $B=\mathbb C^d$、$d\ge1$、逆温度 $\beta>0$、两个自伴算子 $H_0,H_1$，并令
\[
 \tau_i=e^{-\beta H_i}/Z_i,\quad Z_i=\operatorname{Tr}e^{-\beta H_i},\qquad
 H=|0\rangle\langle0|\otimes H_0+|1\rangle\langle1|\otimes H_1.
\]
逻辑空间是 $A=\mathbb C^2$。热校准恢复类 $\mathfrak R$ 包含全部满足
\[
 \mathcal R(|i\rangle\langle i|)=|i\rangle\langle i|\otimes\tau_i
 \quad(i=0,1)
\]
的 CPTP 映射 $\mathcal R:\mathcal B(A)\to\mathcal B(A\otimes B)$。其 Stinespring 环境不受另一个预设小维数限制。逻辑 Hamilton 算子为 $K=\operatorname{diag}(\kappa_0,\kappa_1)$，$\omega=\kappa_0-\kappa_1$。记酉信道为 $\mathcal U_H(t)$、$\mathcal U_K(t)$，取 $\hbar=1$。迹范数 $\|\cdot\|_1$ 不含二分之一，$\|\cdot\|_F$ 是未归一 Hilbert--Schmidt 范数。

**引理 2.2（全恢复类的正块参数化）。** 定义 2.1 的每个恢复，且仅有这些恢复，具有形式
\[
 \mathcal R_X\!\begin{pmatrix}a&b\\c&e\end{pmatrix}
 =\begin{pmatrix}a\tau_0&bX\\cX^\dagger&e\tau_1\end{pmatrix},\qquad
 X=\sqrt{\tau_0}\,M\sqrt{\tau_1},\quad\|M\|\le1.
\]
可见概率全部保持，偏迹后的相干乘数为 $c_X=\operatorname{Tr}X$。对等先验 $|+\rangle$ 与 $|-\rangle$，仅测可见输出的最佳判别错误率为 $(1-|c_X|)/2$。没有协变要求时，
\[
 \max_{\mathcal R\in\mathfrak R}|c_X|
 =f_\beta:=\|\sqrt{\tau_0}\sqrt{\tau_1}\|_1.
\]
全时间协变 $\mathcal U_H(t)\mathcal R=\mathcal R\mathcal U_K(t)$ 等价于
\[
 \boxed{H_0X-XH_1=\omega X.}
\]

**证明。** 任意 Kraus 算子作用于 $|i\rangle$ 的向量必须全部位于 $|i\rangle\otimes B$：它们的外积和在正交补的迹为零，各项正性迫使相应分量为零。故输出只有所列标签块，非对角块由一个矩阵 $X$ 决定。Choi 正性等价于 $\left(\begin{smallmatrix}\tau_0&X\\X^\dagger&\tau_1\end{smallmatrix}\right)\succeq0$；两热态正定，Schur 补将它等价为 $X=\sqrt{\tau_0}M\sqrt{\tau_1}$、$\|M\|\le1$。块对角迹各为一，非对角标签矩阵迹为零，所以该条件还保证迹保持。

偏迹使非对角元乘 $\operatorname{Tr}X$，对两个相位候选，其输出差的迹范数为 $2|c_X|$，两态 Helstrom 公式给判别错误率。迹范数与算子范数的对偶，以及极分解，给无约束最大值 $f_\beta$。该静态可见度结果采用 [OA06] 的既有干涉保真度公式。

校准对角块与相应 $H_i$ 对易，所以协变只需检查 $|0\rangle\langle1|$。其条件是 $e^{-itH_0}Xe^{itH_1}=e^{-it\omega}X$；在零时求导得到盒中式，反向由这个常系数方程的唯一解得到全部时间。[MS14] 的谱模态保持原则给出这一标准选择规则；上述论证同时确定当前通道类的完整参数化。证毕。

## 3. 非对易条件热态的精确自治相干

**定理 3.1（能隙配对与子空间重叠共同决定最优值）。** 令 $H_0=\sum_E E P_E$、$H_1=\sum_F F Q_F$ 为按不同能量值分组的谱分解，允许任意简并和 $[H_0,H_1]\ne0$。在定义 2.1 中固定 $\omega$，则
\[
 \boxed{C_\beta(\omega):=
 \max_{\substack{\mathcal R\in\mathfrak R\\
 \mathcal U_H(t)\mathcal R=\mathcal R\mathcal U_K(t)\ \forall t}}
 |\operatorname{Tr}X|
 =\frac1{\sqrt{Z_0Z_1}}
 \sum_{E-F=\omega} e^{-\beta(E+F)/2}\|P_EQ_F\|_1.}
\]
空和为零。最大值由真实的单个 CPTP 恢复达到。共同本征基中，$\|P_EQ_F\|_1$ 化为公共能量子空间维数，得到相应交换特例。

**证明。** 引理 2.2 及热平方根与相应 Hamilton 算子对易，将协变条件等价为 $H_0M-MH_1=\omega M$。谱块展开后，$M=\sum_{E-F=\omega}P_EMQ_F$。固定 $\omega$ 时，每个 $E$ 至多匹配一个 $F$，每个 $F$ 至多匹配一个 $E$；不同允许块的定义域和像空间两两正交。因此总算子是收缩，当且仅当每个允许块是收缩。

对一个允许块 $N=P_ENQ_F$，迹范数对偶给
\[
 |\operatorname{Tr}N|\le\|P_EQ_F\|_1\,\|N\|.
\]
在 $P_EQ_F$ 的奇异值分解中取支撑上的极部分等距映射，即得到范数至多一、由 $Q_F$ 空间映到 $P_E$ 空间的 $N$，且 $\operatorname{Tr}N=\|P_EQ_F\|_1\ge0$。各块独立选这个极部分，再取正交直和，仍为一个收缩 $M$，并使全部迹项的相位相同。

每块 $X$ 的热系数为 $e^{-\beta(E+F)/2}/\sqrt{Z_0Z_1}$。对迹求和给上界，所构造的 $M$ 同时取到每项上界；引理 2.2 把它变成满足全部校准与协变条件的 CPTP 映射。不同能量子空间不对易时，$\|P_EQ_F\|_1$ 是主夹角余弦之和，而不被误写为交集维数。精确能隙匹配是数学前件，浮点近等值不被当成精确相等。证毕。

**推论 3.2（均值力 Hamilton 选择下的热谱交集）。** 要求逻辑 $\beta$-Gibbs 态等于完整 Gibbs 态的可见边缘时，可取
\[
 K_{\mathrm{mf}}=-\beta^{-1}\operatorname{diag}(\log Z_0,\log Z_1),
 \qquad\omega_{\mathrm{mf}}=\beta^{-1}\log(Z_1/Z_0).
\]
任意热校准恢复都把这个逻辑 Gibbs 态准确送到完整 Gibbs 态。若 $P^{(0)}_\lambda,P^{(1)}_\lambda$ 是两个 $\tau_i$ 在同一正本征值 $\lambda$ 上的谱投影，则同时精确协变的最大可见相干为
\[
 \boxed{C_\beta(\omega_{\mathrm{mf}})
 =\sum_{\lambda\in\operatorname{spec}\tau_0\cap\operatorname{spec}\tau_1}
     \lambda\|P^{(0)}_\lambda P^{(1)}_\lambda\|_1.}
\]
两个热谱没有共同本征值时，该最优值为零。

具体地，令 $H_0=-\Delta Z$、$H_1=-\Delta(\cos\vartheta\,Z+\sin\vartheta\,X)$，其中 $\Delta>0$、$0\le\vartheta\le\pi$，则 $\omega_{\mathrm{mf}}=0$，且
\[
 C_\beta(0)=\cos(\vartheta/2),\qquad
 f_\beta=\sqrt{1-\tanh^2(\beta\Delta)\sin^2(\vartheta/2)}.
\]
对于 $0<\vartheta<\pi$，条件 Hamilton 算子真正非对易；任意有限 $\beta\Delta$ 时，精确自治的相干上限严格小于只作热校准的上限。

**证明。** 逻辑 Gibbs 权重为 $Z_i/(Z_0+Z_1)$，按校准条件恢复后恰得到 $e^{-\beta H}/(Z_0+Z_1)$。能隙条件 $E-F=\beta^{-1}\log(Z_1/Z_0)$ 等价于 $e^{-\beta E}/Z_0=e^{-\beta F}/Z_1=\lambda$；定理 3.1 的权重此时也为 $\lambda$，得到谱交集公式。

所列比特例中两个热态有相同本征值 $p_\pm=(1\pm\tanh(\beta\Delta))/2$。同号能量的两个秩一谱空间，其态向量重叠模为 $\cos(\vartheta/2)$；所以两项之和是 $(p_++p_-)\cos(\vartheta/2)$。二阶密度矩阵的根保真度恒等式 $f^2=\operatorname{Tr}(\tau_0\tau_1)+2\sqrt{\det\tau_0\det\tau_1}$ 给出第二式，两式之差的严格性随 $0<\tanh(\beta\Delta)<1$ 得到。

固定非零 $\Delta$、令 $\beta\downarrow0$ 时，静态最优值趋一，而全时间协变最优值仍为 $\cos(\vartheta/2)$。若令 $\Delta\downarrow0$，每个非零 $\Delta$ 的同一结论也成立，但在 $\Delta=0$ 精确点最优值为一。这种不连续来自精确全时间量词；有限时间误差在下一节单独计量。保 Gibbs 与时间协变仍只是可实现热操作的必要性质或选定放宽类，不构成能量守恒热浴实施的充分证明。证毕。

## 4. 有限预测窗口与完全可区分误差

**定义 4.1（统一预测误差）。** 对固定 $T>0$ 和校准恢复 $\mathcal R_X$，定义
\[
 e_T(\mathcal R_X)=\frac12\sup_{0\le t\le T}
 \|\mathcal U_H(t)\mathcal R_X-\mathcal R_X\mathcal U_K(t)\|_\diamond.
\]
钻石范数允许任意辅助系统、任意联合输入，故该误差不局限于所选训练态。它比较两条先恢复、先演化路径，不是对某个固定参考的熵。令
\[
 Y_t=e^{-itH_0}Xe^{itH_1}-e^{-it\omega}X.
\]

**定理 4.2（全辅助系统误差的精确矩阵表达）。** 对任意定义 2.1 的模型和任意校准恢复，
\[
 \boxed{\|\mathcal U_H(t)\mathcal R_X-\mathcal R_X\mathcal U_K(t)\|_\diamond
       =\|Y_t\|_1.}
\]
因此 $e_T=\tfrac12\sup_{0\le t\le T}\|Y_t\|_1$；不附辅助系统的输入 $|+\rangle$ 已达到每个固定时刻的范数。

再定义时间均方响应缺陷
\[
 a_T(X)^2=T^{-1}\int_0^T\|Y_t\|_F^2dt,
 \quad v(u)=2(1-\operatorname{sinc}u),\quad v(0)=0,
\]
其中 $\operatorname{sinc}u=\sin u/u$。则
\[
 a_T(X)^2=\sum_{E,F}v((E-F-\omega)T)\|P_EXQ_F\|_F^2.
\]
令
\[
 \chi_T^2=\sum_{E-F\ne\omega}
 \frac{\|P_EQ_F\|_F^2}{v((E-F-\omega)T)},
\]
空和为零。对任意校准恢复都有
\[
 \boxed{|\operatorname{Tr}X|
 \le\min\{f_\beta,\ C_\beta(\omega)+\chi_Ta_T(X)\}
 \le\min\{f_\beta,\ C_\beta(\omega)+2\chi_Te_T(\mathcal R_X)\}.}
\]

**证明。** 两条映射在逻辑对角矩阵上相同。对辅助空间上的联合密度矩阵 $\left(\begin{smallmatrix}A&B\\B^\dagger&D\end{smallmatrix}\right)$，它们之差在输出逻辑分块下为
\[
 \begin{pmatrix}0&Y_t\otimes B\\Y_t^\dagger\otimes B^\dagger&0\end{pmatrix}.
\]
其迹范数等于 $2\|Y_t\|_1\|B\|_1$。正块因子分解及 Schatten Cauchy--Schwarz 给 $\|B\|_1\le\sqrt{\operatorname{Tr}A\operatorname{Tr}D}\le1/2$，于是上界是 $\|Y_t\|_1$。该结论也控制钻石范数定义中的一般输入算子：先用 $\left(\begin{smallmatrix}0&Z\\Z^\dagger&0\end{smallmatrix}\right)/2$ 在加倍辅助空间中作 Hermitian 嵌入，再将 Hermitian 算子作正负部分分解，迹范数权重之和不变。输入 $|+\rangle$ 给 $B=1/2$，达到上界。

谱块 $P_EXQ_F$ 在 Hilbert--Schmidt 内积下两两正交，每块相位因子是 $e^{-it(E-F)}-e^{-it\omega}$；平方积分直接给 $v$ 的表达式。$v(u)>0$ 对非零实数 $u$ 成立，所以 $\chi_T$ 在固定有限谱与 $T>0$ 下有限。

只保留匹配块得到 $X_\omega=\sum_{E-F=\omega}P_EXQ_F$。在 $M$ 坐标中这些块有互相正交的定义域和像，故 $\|M_\omega\|\le1$；所以 $X_\omega$ 仍对应一个校准且精确协变的恢复，$|\operatorname{Tr}X_\omega|\le C_\beta(\omega)$。非匹配部分逐块使用 $|\operatorname{Tr}(P_EXQ_F)|\le\|P_EQ_F\|_F\|P_EXQ_F\|_F$，再用带权 Cauchy--Schwarz 得其总迹模至多 $\chi_Ta_T(X)$。静态保真度上界来自引理 2.2。最后 $\|Y_t\|_F\le\|Y_t\|_1\le2e_T$。近能隙导致 $v(\delta T)=\delta^2T^2/3+O(\delta^4T^4)$ 变小；有限精度不能免费认证精确共振。证毕。

**定理 4.3（条件 Ising 热恢复的精确有限时间最优前沿）。** 令 $H_0=gZ$、$H_1=-gZ$、$g\ne0$，使用同一温度 $\beta>0$ 和由热边缘固定的逻辑 $K_{\mathrm{mf}}=0$，忽略其无效常数。记
\[
 f_\beta=\operatorname{sech}(\beta g),\qquad
 m_T=\sin(\min\{|g|T,\pi/2\})>0.
\]
对任意允许误差 $\epsilon\ge0$，在全部定义 2.1 的校准恢复上有
\[
 \boxed{\max_{e_T(\mathcal R)\le\epsilon}|c_X|
       =\min\{f_\beta,\epsilon/m_T\}.}
\]
等号由 $X=(c/2)I_2$、$c=\min\{f_\beta,\epsilon/m_T\}$ 的同一个 CPTP 通道达到。等先验逻辑相位二选一的最优可见错误率因此为
\[
 \boxed{p^*_{\beta,g,T,\epsilon}
 =\tfrac12\left(1-\min\{f_\beta,\epsilon/m_T\}\right).}
\]
此结果已包括任意参考系统对预测误差的检验，不把只在两个校准基态上正确称为全输入预测正确。

**证明。** 在隐藏 $Z$ 基上，若 $X=(x_{jk})$，则
\[
 Y_t=\operatorname{diag}((e^{-2igt}-1)x_{00},(e^{2igt}-1)x_{11}).
\]
两个非对角矩阵元满足零能隙，所以相位误差恰为零。定理 4.2 因而给
\[
 e_T(\mathcal R_X)=m_T(|x_{00}|+|x_{11}|).
\]
正块校准又给 $|x_{jj}|\le\sqrt{(\tau_0)_{jj}(\tau_1)_{jj}}=f_\beta/2$。因此 $|c_X|\le|x_{00}|+|x_{11}|\le\min\{f_\beta,\epsilon/m_T\}$。

取 $X=(c/2)I_2$，相应 $M=(c/f_\beta)I_2$ 是收缩，所以它确实定义 CPTP 恢复。其相干为 $c$，误差恰为 $m_Tc$，达到上界。相位判别式由引理 2.2。$\epsilon=0$、$T>0$ 时最优相干为零，恢复已知全时间判据；固定容差下的小窗口则可能容许静态最优。所有校准恢复在任意逻辑对角输入上产生相同输出，所以只用这些输入的概率或平衡损失训练，不能辨认前沿上的位置；需要相位任务或动态检验。

该前沿是选定 CPTP 类中的优化，不证明所有达到通道可由无额外资源的热操作实施；控制器、工作源和时间参考的成本未计入 $\epsilon$。证毕。

## 5. 来源、适用范围与未闭合问题

[OA06] Daniel K. L. Oi、Johan Aberg，*Fidelity and Coherence Measures from Interference*，Physical Review Letters 97, 220404 (2006)，DOI [10.1103/PhysRevLett.97.220404](https://doi.org/10.1103/PhysRevLett.97.220404)。式 (6) 的一般 subspace-preserving 可见度最大值是根保真度；更窄的局部准备类有不同上限。

[MS14] Iman Marvian、Robert W. Spekkens，*Modes of asymmetry: the application of harmonic analysis to symmetric quantum dynamics and quantum reference frames*，Physical Review A 90, 062110 (2014)，DOI [10.1103/PhysRevA.90.062110](https://doi.org/10.1103/PhysRevA.90.062110)。第 II 节式 (2.7)--(2.10) 给出时间对称通道的频率模态保持规则。

[LJR15] Matteo Lostaglio、David Jennings、Terry Rudolph，*Description of quantum coherence in thermodynamic processes requires constraints beyond free energy*，Nature Communications 6, 6383 (2015)，DOI [10.1038/ncomms7383](https://doi.org/10.1038/ncomms7383)。Theorem 1 及 Methods 给出相关时间平移约束。

[FOR15] Philippe Faist、Jonathan Oppenheim、Renato Renner，*Gibbs-Preserving Maps outperform Thermal Operations in the quantum regime*，New Journal of Physics 17, 043003 (2015)，DOI [10.1088/1367-2630/17/4/043003](https://doi.org/10.1088/1367-2630/17/4/043003)。其结论限定了 Gibbs 保持映射的热力学解释。

[NMLW25] Theshani Nuradha、Hemant K. Mishra、Felix Leditzky、Mark M. Wilde，*Multivariate Fidelities*，Journal of Physics A: Mathematical and Theoretical 58(16), 165304 (2025)，DOI [10.1088/1751-8121/adc645](https://doi.org/10.1088/1751-8121/adc645)。第 5 节给出正块半定规划，第 6 节提出相关操作解释问题。

[BO15] Cedric Beny、Tobias J. Osborne，*The renormalisation group via statistical inference*，New Journal of Physics 17, 083005 (2015)，DOI [10.1088/1367-2630/17/8/083005](https://doi.org/10.1088/1367-2630/17/8/083005)。其有限观察与统计可区分性框架只提供尺度解释背景。

本卷的精确谱匹配不等于数值近匹配，有限时间误差预算不等于真实耗热，允许任意 CPTP 恢复不等于免费物理实施。仍未闭合的问题包括一般非对易多标签的共同动态最优值、一般模型的有限窗口完整 Pareto 前沿，以及实际能量守恒实现的工作与参考系成本。

## 追加锚（本行以下为增补区）
