# The Maximal Spectral Sharpness Theorem

## Abstract

Spectral sharpness is the attained distance-normalized capacity, with its median-cut witness, qubit formula, endpoints, and data-processing law.

**Theorem 1.1 (Spectral sharpness is the attained normalized capacity).**

$$\begin{gathered}\forall n \in \mathbb{N}, r: \operatorname{Fin}({n+2})\to\mathbb{R},\\(\forall i, 0 \le r_i) \land \operatorname{Antitone}(r) \land \sum_ir_i=1 \Rightarrow\\(\forall a: \operatorname{Fin}({n+2})\to\mathbb{R}, \operatorname{Antitone}(a) \Rightarrow \operatorname{IsLeast}(\left\{d \mid \exists c \in \mathbb{R}, \forall i, \lvert a_i-c \rvert \le d\right\}, D(a))) \land\\\operatorname{IsGreatest}(\left\{v \mid \exists a: \operatorname{Fin}({n+2})\to\mathbb{R}, \operatorname{Antitone}(a) \land 0 < D(a) \land \frac{C_{a}(r)}{D(a)}=v\right\}, \operatorname{Sharp}(r)) \land\\((\forall i, Q_n(i)=1 \lor Q_n(i)=-1) \land \operatorname{Antitone}(Q_n) \land \frac{C_{Q_n}(r)}{D(Q_n)}=\operatorname{Sharp}(r)) \land\\(\forall q: \operatorname{Fin}(2)\to\mathbb{R}, \sum_iq_i=1 \Rightarrow \operatorname{Sharp}(q)=\sqrt{2\sum_iq_i^{2}-1}) \land\\(\operatorname{Sharp}(r)=1 \iff \lvert\left\{i \mid r_i \neq 0\right\}\rvert \le \frac{{n+2}}{2}) \land\\(\operatorname{Sharp}(r)=0 \iff \forall i, r_i=\frac{1}{{n+2}}) \land\\(\forall r': \operatorname{Fin}({n+2})\to\mathbb{R}, S: \operatorname{Matrix}(\operatorname{Fin}({n+2}), \operatorname{Fin}({n+2}), \mathbb{R}), \operatorname{Antitone}(r') \land \operatorname{DS}(S) \land r=Sr' \Rightarrow \operatorname{Sharp}(r) \le \operatorname{Sharp}(r')).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Sharpness/MaximalSpectralSharpness.maximal_spectral_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let r be a nonnegative, nonincreasing, unit-sum spectrum in dimension N = n + 2. Its spectral sharpness Sharp(r) is one half the l1 distance from r to its reversal. For a nonincreasing observable spectrum a, D(a) is half its endpoint range. The first clause identifies D(a) as the least uniform bound on distance from a constant spectrum, so it is exactly the operator-norm distance from the observable to the center.

Sharp(r) is the greatest attained value of C_a(r)/D(a) over noncentral nonincreasing observables. The explicit median-cut question Q_n has only plus-or-minus-one values, is nonincreasing, has D(Q_n) = 1, and attains the greatest value. Thus the variational maximum and the yes/no maximizer are both addressable parts of the public statement.

For a two-point unit-sum spectrum q, Sharp(q) equals the square root of twice its quadratic purity minus one, the spectral form of the qubit Bloch radius. The same statement gives Sharp(r) = 1 exactly when the nonzero support has size at most N/2, and Sharp(r) = 0 exactly when r is uniform.

Finally, if r = S r' for a doubly stochastic matrix S and both spectra are nonincreasing, then Sharp(r) <= Sharp(r'). This is the spectral majorization form of the unital-channel data-processing law. The proof uses the same median question on both sides and applies the frozen spectral-pairing comparison, rather than introducing a second channel or majorization carrier.

Dimension at least two is encoded by N = n + 2 because the normalized ratio ranges over observables outside the center. The numerical trials and decimal certificate accompanying the source statement are empirical checks and are not theorem clauses.

## References

- Truth anchor: `D5/S3/Quantum/Sharpness/MaximalSpectralSharpness.maximal_spectral_sharpness`
- Dependency: [D5/S3/Quantum/Sharpness/SpectralSharpnessDuality](SpectralSharpnessDuality.md)
- Dependency: [D5/S3/Quantum/Sharpness/SpectralSharpnessSaturation](SpectralSharpnessSaturation.md)
