# Exact Binary Raney Zero Runs

## Abstract

The literal Raney sequence R(3,1) modulo two has exactly the positive maximal zero-run lengths floor(2^m/3), with explicit earliest record intervals.

The binary clause of Ma and Zhang's Complete small-prime record spectra for R(3,1): proofs concerns the literal natural quotient raneyNumber(3,1,n), reduced modulo two only after the integral division. Write rho(n) for this residue and Z(a,b) for IsMaximalDeltaInterval({0},rho,a,b). Thus a<=b, every index in [a,b] has residue zero, the right neighbor has nonzero residue, and either a=0 or the left neighbor has nonzero residue. Here rho(0)=1, so the a=0 alternative cannot occur.

For natural m, let L(m)=floor(2^m/3) and A(m)=ceil(2^(m+1)/3)=(2^(m+1)+2)/3, with natural division. The theorem quantifies over every finite nonempty maximal interval at every natural index. A record uses the source's weak comparison with earlier runs, allowing ties; the displayed earliest occurrence satisfies the stronger strict comparison.

**Theorem 1.1 (Complete Binary Spectrum and Earliest Records).**

$$\left((\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \operatorname{Z}\left(a, b\right) \Rightarrow \left(\exists m \in \mathbb{N},\; \left(2 \le m \land b + 1 - a = \operatorname{NatDiv}\left(2^{m}, 3\right)\right) \land \operatorname{NatDiv}\left(2^{m + 1} + 2, 3\right) \le a\right)) \land (\forall m \in \mathbb{N},\; 2 \le m \Rightarrow \left(\left(\operatorname{Z}\left(\operatorname{NatDiv}\left(2^{m + 1} + 2, 3\right), 2^{m} - 1\right) \land 2^{m} - 1 + 1 - \operatorname{NatDiv}\left(2^{m + 1} + 2, 3\right) = \operatorname{NatDiv}\left(2^{m}, 3\right)\right) \land \left(\forall a \in \mathbb{N},\; \forall b \in \mathbb{N},\; \left(\operatorname{Z}\left(a, b\right) \land a < \operatorname{NatDiv}\left(2^{m + 1} + 2, 3\right)\right) \Rightarrow b + 1 - a < \operatorname{NatDiv}\left(2^{m}, 3\right)\right)\right))\right) \land (\forall m \in \mathbb{N},\; \forall k \in \mathbb{N},\; \left(2 \le m \land m < k\right) \Rightarrow \operatorname{NatDiv}\left(2^{m}, 3\right) < \operatorname{NatDiv}\left(2^{k}, 3\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Raney/ExactBinaryRuns.raney_binary_exact_zero_run_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual maximal zero interval [a,b] has length L(m) for some m>=2 and a>=A(m). Conversely, [A(m),2^m-1] is an actual maximal zero interval of length L(m) for every m>=2. Every maximal interval beginning before A(m) has strictly smaller length. Finally, L(m)<L(k) whenever 2<=m<k. These statements give equality of the positive maximal-run spectrum and the distinct positive record spectrum, with no repeated retained lengths.

The proof establishes the integral adjacent-binomial identity before taking residues. Lucas's theorem then gives support at 2n exactly when there is support at n, support at 4n+1 exactly when there is support at n, and no support at 4n+3. These are identities about the literal Raney sequence; no mask or correctness assumption is supplied.

The top half of each binary prefix has the support of a translated shorter prefix. Its greatest supported index is floor(2^(m+1)/3). A positive gap between consecutive supported indices either descends to a shorter prefix, translates to one, or is the terminal gap. The descent covers every finite gap and tracks the right endpoint 2^m as a lower bound, which supplies the first-occurrence bound. The terminal gap has both actual nonzero neighbors. This document asserts only the binary clause; the ternary and larger-prime clauses require their own proofs.

## References

- Truth anchor: `D5/S1/Recurrence/Raney/ExactBinaryRuns.raney_binary_exact_zero_run_spectrum`
- Dependency: [D5/S1/Recurrence/Raney/ZeroRunFamilies](ZeroRunFamilies.md)
