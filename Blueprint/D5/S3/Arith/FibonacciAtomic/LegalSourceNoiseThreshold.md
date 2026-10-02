# Sharp Update Noise Threshold for Legal Windows

## Abstract

Legal five-window sources admit exact current-row recovery precisely below a sharp update-noise budget.

Fix a rational decay lambda with 0<lambda<1, embedded in the real numbers. Words use the low-to-high windows 000,100,010,101,001. A word is legal when no high bit of one window and low bit of the next are both one. The empty word is legal. Terminal zero windows remain in the source. The symbolic run starts with both flags false; End is queried after the entire word.

The canonical rows are zA=(0,1,1), zB=(1,1,1), zC=(1,0,1), and zD=(0,0,0). The original matrices are the outer products e3*zA, e2*zB, e3*zB, e2*zC, e3*zC for 000,100,010,101,001 respectively. Their row actions agree with the symbolic transitions on every word, including failed seams. Legal words reach A, B or C; End is false at A and true at B and C.

An actual trajectory starts at zA without initial noise. Each letter applies lambda times its original row action and then adds an arbitrary real three-vector whose sup norm is at most nu, where nu>=0. Noise is bounded separately at every step. The accumulated geometric sum and critical budget are as follows.

$$
\begin{aligned}\operatorname{s}\left(n\right) = \sum_{0 \le j < n}\lambda^{j}\\\operatorname{c}\left(n\right) = \frac{\lambda^{n}}{\operatorname{s}\left(n\right) + 1}\end{aligned}
$$

**Theorem 1.1 (One Current Row Decoder, All Allowed Trajectories).**

$$\begin{aligned}\forall \lambda \in \mathbb{Q}, 0 < \lambda < 1 \Rightarrow\\\forall nu \in \mathbb{R}, nu \ge 0 \Rightarrow \forall M \in \mathbb{N}, \forall b \in \operatorname{Bool},\\\operatorname{Rstate}\left(\lambda, nu, M, b\right) \Leftrightarrow (M = 0 \lor nu < \operatorname{c}\left(M\right))\\\operatorname{RclockState}\left(\lambda, nu, M, b\right) \Leftrightarrow (M = 0 \lor nu < \operatorname{c}\left(M\right))\\\operatorname{Rend}\left(\lambda, nu, M, b\right) \Leftrightarrow (M = 0 \lor nu < \operatorname{c}\left(M\right))\\\operatorname{RclockEnd}\left(\lambda, nu, M, b\right) \Leftrightarrow (M = 0 \lor nu < \operatorname{c}\left(M\right))\\\operatorname{Rstate}\left(\lambda, nu, 0, b\right), (\operatorname{Rstate}\left(\lambda, nu, 1, b\right) \Leftrightarrow nu < \frac{\lambda}{2})\\\operatorname{RclockState}\left(\lambda, nu, 0, b\right), (\operatorname{RclockState}\left(\lambda, nu, 1, b\right) \Leftrightarrow nu < \frac{\lambda}{2})\\\operatorname{Rend}\left(\lambda, nu, 0, b\right), (\operatorname{Rend}\left(\lambda, nu, 1, b\right) \Leftrightarrow nu < \frac{\lambda}{2})\\\operatorname{RclockEnd}\left(\lambda, nu, 0, b\right), (\operatorname{RclockEnd}\left(\lambda, nu, 1, b\right) \Leftrightarrow nu < \frac{\lambda}{2})\\M \ge 2 \Rightarrow \frac{\lambda^{M}}{2 \times \operatorname{s}\left(M\right)} < \operatorname{c}\left(M\right)\\\lim_{k \to \infty} \operatorname{c}\left(k\right) = 0\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/LegalSourceNoiseThreshold.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rstate and Rend mean existence of a total decoder from the current real row to the canonical state row or Boolean End label. RclockState and RclockEnd additionally give the decoder the current position. For each fixed lambda, nu and M, one decoder must work for every legal input and every permitted noise sequence. It receives no current letter, history, previous state or separate memory. The Boolean b selects all lengths n<=M when false, and only length n=M when true.

For a nonempty legal trajectory of length n, every target zero coordinate has magnitude at most nu: the last matrix has cleared its earlier value. Every target one coordinate is at least lambda^n-nu*s(n). The induction reads a coordinate equal to one in the legal preceding canonical state. Below c(M), a single threshold strictly between nu and lambda^M-nu*s(M) separates all zero and one coordinates. This threshold lies between zero and one, so it also decodes the empty word.

At c=c(M) with M>=1, use the legal words (100)^M and (000)^M. The first trajectory adds -c*zB at every step. The second adds -c*zA for its first M-1 steps, then (c,-c,-c). Their actual final rows are both c*zB, although their canonical targets are B and A and their End labels are true and false. Every disturbance obeys the budget c, so the same collision is permitted at any larger budget. The position also agrees, which excludes every decoder under either observation contract.

At depth zero there is no update and a constant decoder works for every budget. At depth one the strict boundary is lambda/2. For M>=2 the legal-source budget exceeds lambda^M/(2*s(M)). The budgets tend to zero, so a fixed positive stepwise budget cannot support current-row recovery at every depth.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/LegalSourceNoiseThreshold.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/BalancedPhaseMissingResidue](BalancedPhaseMissingResidue.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd](LiteralWindowEnd.md)
- Dependency: [D5/S3/Observer/SymbolicStability/SmoothFiniteMachineRealization](../../Observer/SymbolicStability/SmoothFiniteMachineRealization.md)
