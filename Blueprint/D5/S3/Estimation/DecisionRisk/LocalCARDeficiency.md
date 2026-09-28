# Local CAR Deficiency

## Abstract

A local change of a CAR profile preserves every pair readout and has two exact directed deficiencies.

**Theorem 1.1 (Exact local deficiencies in an arbitrary common background).**

$$\begin{gathered}\forall A: \operatorname{Type}\left(\right), (\operatorname{Fintype}\left(A\right)) \Rightarrow\\{}(\operatorname{DecidableEq}\left(A\right)) \Rightarrow\\{}(\operatorname{Nonempty}\left(A\right)) \Rightarrow\\{}(\forall U: \operatorname{Finset}\left(A\right), \forall a: \mathbb{R}, \forall w: \operatorname{Block}\left(A\right) \to \mathbb{R}, (((3 \leq \operatorname{card}\left(U\right)) \land\\{}(0 \leq a) \land\\{}(\forall B: \operatorname{Block}\left(A\right), 0 \leq w\left(B\right)) \land\\{}(\forall i: A, \operatorname{sum}\left(B, \operatorname{Block}\left(A\right), \operatorname{experiment}\left(w, i, B\right)\right) = 1) \land\\{}(\forall B: \operatorname{Block}\left(A\right), (\operatorname{subset}\left(B, U\right)) \Rightarrow\\{}(\operatorname{card}\left(B\right) = 2) \Rightarrow\\{}(a \leq w\left(B\right))))) \Rightarrow\\{}(\text{let }v = \operatorname{plus}\left(w, U, a\right) , ep = \frac{a \cdot (\operatorname{card}\left(U\right) - 2)}{\operatorname{card}\left(U\right)} , em = \frac{a \cdot (\operatorname{card}\left(U\right) - 2)}{2} \text{ in }\\{}((\forall B: \operatorname{Block}\left(A\right), 0 \leq v\left(B\right)) \land\\{}(\forall i: A, \operatorname{sum}\left(B, \operatorname{Block}\left(A\right), \operatorname{experiment}\left(v, i, B\right)\right) = 1) \land\\{}(\forall i: A, \forall j: A, (i \neq j) \Rightarrow\\{}(\operatorname{r}\left(v, i, j\right) = \operatorname{r}\left(w, i, j\right))) \land\\{}(\operatorname{finiteDeficiency}\left(\operatorname{experiment}\left(w\right), \operatorname{experiment}\left(v\right)\right) = \operatorname{ofReal}\left(ep\right)) \land\\{}(\operatorname{finiteDeficiency}\left(\operatorname{experiment}\left(v\right), \operatorname{experiment}\left(w\right)\right) = \operatorname{ofReal}\left(em\right)) \land\\{}(\exists KP, KM: \operatorname{FiniteMarkovKernel}\left(\operatorname{Block}\left(A\right), \operatorname{Block}\left(A\right)\right),\\{}((\forall i: A, \operatorname{totalVariation}\left(\operatorname{experiment}\left(w\right)\left(i\right), \operatorname{channelOutput}\left(KP.1, \operatorname{experiment}\left(v\right)\left(i\right)\right)\right) = \operatorname{ite}\left(\operatorname{member}\left(i, U\right), ep, 0\right)) \land\\{}(\forall i: A, \operatorname{totalVariation}\left(\operatorname{experiment}\left(v\right)\left(i\right), \operatorname{channelOutput}\left(KM.1, \operatorname{experiment}\left(w\right)\left(i\right)\right)\right) = \operatorname{ite}\left(\operatorname{member}\left(i, U\right), em, 0\right)) \land\\{}(\forall K: \operatorname{FiniteMarkovKernel}\left(\operatorname{Block}\left(A\right), \operatorname{Block}\left(A\right)\right), ep \leq \operatorname{uniformSimulationError}\left(\operatorname{experiment}\left(w\right), \operatorname{experiment}\left(v\right), K\right)) \land\\{}(\forall K: \operatorname{FiniteMarkovKernel}\left(\operatorname{Block}\left(A\right), \operatorname{Block}\left(A\right)\right), em \leq \operatorname{uniformSimulationError}\left(\operatorname{experiment}\left(v\right), \operatorname{experiment}\left(w\right), K\right))))))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/LocalCARDeficiency.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is any finite nonempty state set, and Block(A) consists of all nonempty subsets of A. For a profile w, experiment(w,i,B) is w(B) when i belongs to B and is zero otherwise. The profile is nonnegative and each experiment row sums to one. No partition-mixture representation is assumed.

Fix U contained in A with m = card(U) at least three. The local direction is one at U, m minus two at each singleton in U, minus one at each two-element block contained in U, and zero elsewhere. The new profile is v = w + a direction(U), where a is nonnegative. The capacity hypothesis applies only to the weight of each exact internal two-element block; it is not a bound on the sum of weights of all blocks containing that pair.

$$
\begin{gathered}\operatorname{direction}\left(U, B\right) = \operatorname{ite}\left(B = U, 1, \operatorname{ite}\left(\operatorname{subset}\left(B, U\right) \land \operatorname{card}\left(B\right) = 1, \operatorname{card}\left(U\right) - 2, \operatorname{ite}\left(\operatorname{subset}\left(B, U\right) \land \operatorname{card}\left(B\right) = 2, -1, 0\right)\right)\right)\\{}\operatorname{plus}\left(w, U, a, B\right) = w\left(B\right) + a \cdot \operatorname{direction}\left(U, B\right)\end{gathered}
$$

The common background is arbitrary, including blocks meeting both U and its complement. Every pair of distinct states in A has the same readout r before and after the change. The new profile is nonnegative and normalized at every state.

$$
\operatorname{r}\left(w, i, j\right) = \operatorname{sum}\left(B, \operatorname{Block}\left(A\right), \operatorname{ite}\left(\operatorname{member}\left(i, B\right) \land \operatorname{member}\left(j, B\right), w\left(B\right), 0\right)\right)
$$

finiteDeficiency takes its target experiment first and its source experiment second. It is the infimum, over all stochastic kernels on the full nonempty-block alphabet, of the maximum statewise half-L1 total-variation error. Thus finiteDeficiency(experiment(w),experiment(v)) describes simulation from v to w, and the reverse expression describes simulation from w to v. The lower bounds in the statement hold separately for every unrestricted kernel, including kernels that output target zero-weight blocks or blocks not containing the true state.

There is one globally defined attaining kernel in each direction, used for all states simultaneously. Write Q for the two-element blocks contained in U, let delta(B,C) be one when B equals C and zero otherwise, and write indicator(P) for the indicator of a condition. Set b(B) = w(B) - a indicator(B in Q). The following probability rows and nonnegative mass flows give explicit attaining kernels.

$$
\begin{gathered}m = \operatorname{card}\left(U\right), b\left(B\right) = w\left(B\right) - a \cdot \operatorname{indicator}\left(\operatorname{member}\left(B, Q\right)\right)\\{}\operatorname{P}\left(C\right) = \operatorname{indicator}\left(\operatorname{member}\left(C, Q\right)\right) \cdot \frac{2}{m \cdot (m - 1)}\\{}\operatorname{S}\left(j, C\right) = \frac{\operatorname{indicator}\left(\operatorname{member}\left(C, Q\right) \land \operatorname{member}\left(j, C\right)\right)}{m - 1}\\{}\operatorname{FP}\left(B, C\right) = b\left(B\right) \cdot \operatorname{delta}\left(B, C\right) + a \cdot \operatorname{indicator}\left(B = U\right) \cdot \operatorname{P}\left(C\right) + a \cdot (m - 2) \cdot \operatorname{sum}\left(j, U, \operatorname{indicator}\left(B = \operatorname{singleton}\left(j\right)\right) \cdot \operatorname{S}\left(j, C\right)\right)\\{}\operatorname{FM}\left(B, C\right) = b\left(B\right) \cdot \operatorname{delta}\left(B, C\right) + a \cdot \operatorname{indicator}\left(\operatorname{member}\left(B, Q\right)\right) \cdot (\frac{\operatorname{delta}\left(U, C\right)}{m - 1} + \frac{m - 2}{2 \cdot (m - 1)} \cdot \operatorname{sum}\left(j, B, \operatorname{delta}\left(\operatorname{singleton}\left(j\right), C\right)\right))\\{}\operatorname{KP}\left(B, C\right) = \operatorname{ite}\left(v\left(B\right) = 0, \operatorname{delta}\left(B, C\right), \frac{\operatorname{FP}\left(B, C\right)}{v\left(B\right)}\right)\\{}\operatorname{KM}\left(B, C\right) = \operatorname{ite}\left(w\left(B\right) = 0, \operatorname{delta}\left(B, C\right), \frac{\operatorname{FM}\left(B, C\right)}{w\left(B\right)}\right)\end{gathered}
$$

P is uniform on Q, and S(j) is uniform on its blocks containing j, for j in U. The row sums of FP and FM are respectively v(B) and w(B). When an input weight is zero, its entire nonnegative flow row is zero; the displayed identity row completes the kernel on that input. Consequently both kernels are defined on every input block. For a = 0 both constructions are the identity kernel and both errors are zero. No division by a is required.

KP has error ep = a(m-2)/m at every state in U and zero error at every state outside U. KM has error em = a(m-2)/2 at every state in U and zero outside U. Both retain every background block outside the changed coordinates, including all crossing blocks.

For optimality, put k(B) = card(B intersect U). Two bounded losses on the full output alphabet have optimal unnormalized block costs max(k(B)-2,0) and, respectively, zero for k(B) at most one and k(B)/2 otherwise. The identity decision attains each block cost. Averaging over the uniform prior on U gives risk gaps ep in the first direction and em in the second. All unchanged background terms cancel separately. Bounded-loss risk transport bounds each gap by the maximum statewise simulation error of every stochastic kernel, giving the two lower bounds and hence equality with the explicit upper bounds.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/LocalCARDeficiency.result`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer](../SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.md)
