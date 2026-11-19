# Positive One-Mode Williamson Form

## 17. 正定单模二次能量的辛正则形

**引理 17.1（正定单模 Williamson 正则形）。** 对任意实数 $a,b,c$，取物理 $q,p$ 顺序的辛矩阵

$$
J_1=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
S=\begin{pmatrix}a&b\\b&c\end{pmatrix}.
$$

若 $S$ 严格正定，则存在实数 $\omega>0$ 和同一个实矩阵 $M\in\mathbb R^{2\times2}$，同时满足

$$
M^T J_1 M=J_1,\qquad M^T S M=\omega I_2.
$$

证明：正定性给出 $a>0$ 和 $\delta=ac-b^2>0$。令 $\omega=\sqrt\delta$、$u=\sqrt{\omega/a}>0$，并取

$$
M=\begin{pmatrix}u&-b/(au)\\0&1/u\end{pmatrix}.
$$

此时 $au^2=\omega$、$\omega^2=ac-b^2$；逐项相乘得到两条所述矩阵恒等式。严格正定前件排除退化矩阵和零频率。该引理只处理一个正则模式；一般有限模的相容 Williamson 分解以及 Schrödinger 表示中的无界算子和热态结论仍需各自的证明。

## 追加锚（本行以下为增补区）
