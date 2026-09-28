# Approximate CAR recovery

## Abstract

One approximate coarsening-at-random simulation admits a common reverse kernel with a signed pairwise recovery budget.

**Definition 1.1 (Nonempty blocks).**

$$\forall A: \mathrm{Type}, \operatorname{Block}(A) = \{B: \operatorname{Finset}(A) \mid \operatorname{Nonempty}(B)\}.$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.Block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output alphabet consists of all nonempty finite subsets of the state space. Blocks of zero weight remain in the alphabet.

**Definition 1.2 (CAR rows).**

$$\forall A: \mathrm{Type}, \operatorname{DecidableEq}(A) \Rightarrow \forall w: \operatorname{Block}(A) \to \mathbb{R}, i: A, B: \operatorname{Block}(A),\\{}\operatorname{row}(w, i, B) = \begin{cases}w(B)&i \in B\\0&\text{otherwise}\end{cases}.$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.row` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A state assigns weight w(B) to a block containing it and zero to every other block. Nonnegative weights and unit row sums make these probability rows.

**Definition 1.3 (Pairwise block weights).**

$$\forall A: \mathrm{Type}, \operatorname{Fintype}(A) \Rightarrow \operatorname{DecidableEq}(A) \Rightarrow \forall w: \operatorname{Block}(A) \to \mathbb{R}, i: A, j: A,\\{}\operatorname{pair}(w, i, j) = \sum_{{B: \operatorname{Block}(A)}} {\begin{cases}w(B)&((i \in B) \land (j \in B))\\0&\text{otherwise}\end{cases}}.$$

*Formalization.* `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.pair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pair weight sums the weights of blocks containing both states; the definition also includes equal states.

**Theorem 1.4 (Common reverse kernel and signed recovery bound).**

$$\forall A: \mathrm{Type}, \operatorname{Fintype}(A) \Rightarrow \operatorname{DecidableEq}(A) \Rightarrow \operatorname{Nonempty}(A) \Rightarrow\\{}\forall w: \operatorname{Block}(A) \to \mathbb{R}, v: \operatorname{Block}(A) \to \mathbb{R}, H: \operatorname{FiniteMarkovKernel}(\operatorname{Block}(A), \operatorname{Block}(A)),\\{}((\forall B: \operatorname{Block}(A), 0 \leq w(B)) \land (\forall C: \operatorname{Block}(A), 0 \leq v(C)) \land (\forall i: A, \sum_{{B: \operatorname{Block}(A)}} {\operatorname{row}(w, i, B)} = 1) \land (\forall i: A, \sum_{{C: \operatorname{Block}(A)}} {\operatorname{row}(v, i, C)} = 1)) \Rightarrow\\{}\text{let} \varepsilon = i \mapsto \operatorname{totalVariation}(\operatorname{channelOutput}(H.1, \operatorname{row}(w, i)), \operatorname{row}(v, i)),\\{}\Delta = i j \mapsto (\operatorname{pair}(v, i, j)) - (\operatorname{pair}(w, i, j)),\\{}b = i \mapsto (\frac{1}{2}) \cdot (\sum_{{j \in A, j \neq i}} {((\Delta(i, j)) + (\varepsilon(i)) + (\varepsilon(j)))}),\\{}\varepsilon_{max} = \max_{{i \in A}} {\varepsilon(i)}, eta = \max_{{i,j \in A}} {\begin{cases}0&i = j\\\lvert\Delta(i, j)\rvert&\text{otherwise}\end{cases}}, b_{max} = \max_{{i \in A}} {b(i)}\\{}\text{in} \exists R: \operatorname{FiniteMarkovKernel}(\operatorname{Block}(A), \operatorname{Block}(A)),\\{}((\forall i: A, j: A, 0 \leq (\Delta(i, j)) + (\varepsilon(i)) + (\varepsilon(j))) \land (\forall i: A, \operatorname{totalVariation}(\operatorname{channelOutput}(R.1, \operatorname{row}(v, i)), \operatorname{row}(w, i)) \leq b(i)) \land (\operatorname{finiteDeficiency}(\operatorname{row}(w), \operatorname{row}(v)) \leq \operatorname{ofReal}(\operatorname{min}(1, b_{max}))) \land (\operatorname{min}(1, b_{max}) \leq \operatorname{min}(1, (\frac{(((\operatorname{card}(A)) - (1))) \cdot (eta)}{2}) + ((((\operatorname{card}(A)) - (1))) \cdot (\varepsilon_{max})))) \land ((\forall i: A, \varepsilon(i) = 0) \Rightarrow \forall B: \operatorname{Block}(A), C: \operatorname{Block}(A), 0 < v(C) \Rightarrow R.1(C, B) = \begin{cases}\frac{(\operatorname{card}(B)) \cdot (((w(B)) \cdot (H.1(B, C))))}{(\operatorname{card}(C)) \cdot (v(C))}&B \subseteq C\\0&\text{otherwise}\end{cases})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state space A is finite and nonempty, with decidable equality. Both profiles have nonnegative weights and unit row sums. The one forward Markov kernel H is shared by every state, and the existentially quantified reverse kernel R is shared by all conclusions. Kernel arguments are ordered as input then output. Total variation is half the sum of absolute coordinate differences.

Delta is signed: it is the pair weight for v minus the pair weight for w. Only Delta(i,j) + epsilon(i) + epsilon(j) is asserted nonnegative. The function eta is the maximum absolute off-diagonal pair difference, with diagonal entries set to zero. Thus eta and each empty row sum are zero on a one-state space, and the recovery error is zero there.

The deficiency has target row(w) and source row(v): it measures simulation of w from v. It is the infimum over all reverse Markov kernels of the maximum statewise total-variation error, embedded in the extended nonnegative reals. The bound is truncated at one.

For the construction, put F_i(B,C) = row(w,i,B) H(B,C) and Q_i(C) = sum_B F_i(B,C). Multiply each column by a_i(C) = min(1,V_i(C)/Q_i(C)) when Q_i(C) is positive, and by one when it is zero, obtaining t_i. The nonnegative residuals u_i(B) = W_i(B) - sum_C t_i(B,C) and z_i(C) = V_i(C) - sum_B t_i(B,C) both have total mass epsilon(i). For positive epsilon(i), set g_i = t_i + u_i z_i / epsilon(i). When epsilon(i) is zero, both residuals vanish and g_i = t_i; no division by zero is needed.

The table g_i has marginals W_i and V_i and is supported on blocks containing i. The overlap of g_i and g_j is at least pair(w,i,j) - epsilon(i) - epsilon(j). Consequently their columnwise half-L1 difference, summed over columns containing both states, is at most the signed budget Delta(i,j) + epsilon(i) + epsilon(j).

For v(C) > 0 choose R(C,B) = sum_{j in C} g_j(B,C) / (|C| v(C)). For v(C) = 0 choose a point mass at one fixed singleton block; such columns carry no mass under any V_i. Averaging the tables on C and using |C| >= 2 for distinct states in C yields the factor one half in the signed row budget.

If every epsilon(i) is zero, then g_i = F_i. The very same R reduces on every positive-weight column to the displayed subset formula, and is zero when B is not contained in C. Its zero-weight rows remain arbitrary probability rows. No positive lower bound on block weights and no optimality of the coefficients are assumed.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.Block`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.pair`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.result`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.row`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer](../SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.md)
