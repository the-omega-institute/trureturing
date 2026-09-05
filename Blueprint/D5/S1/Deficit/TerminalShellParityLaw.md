# Terminal Shell Parity Law

## Abstract

Under the terminal first-sign law, defect status is exactly odd shell parity.

**Theorem 1.1 (Terminal defect is equivalent to odd shell parity).**

$$\begin{aligned}\forall K, a\in \mathbb{N}, terminalSign\in \mathbb{Z},\\0 < K \land terminalSign = {-1}^{K - 1 + a} \Rightarrow\\terminalSign = {-1}^{a} \iff \operatorname{Odd}\left(K\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/TerminalShellParityLaw.terminal_shell_defect_iff_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer terminalSign represents the sign of the source tail term. The premise records the first-sign law exactly: terminalSign equals (-1) raised to K-1+a. Defect is the equality with (-1)^a.

The positive-shell hypothesis is essential. Lean natural subtraction truncates at zero, and at K=0 the displayed sign equality holds even though Odd(K) is false. Writing 0<K removes that false branch.

After expressing K as a successor, Mathlib's even and odd negative-one power laws reduce the statement to successor parity. The same module also proves that the opposite terminal sign occurs exactly for even K. Numerical root scans, window errors, and the open middle region are not asserted.

## References

- Truth anchor: `D5/S1/Deficit/TerminalShellParityLaw.terminal_shell_defect_iff_odd`
