# Exact CAR revelation scaling

## Abstract

Mixing CAR experiments with complete revelation scales both directed deficiencies exactly and gives ordinary partition realizations on one public product seed.

**Theorem 1.1 (Two directed equalities and a common partition seed).**

$$\begin{gathered}\forall A: Type_{u}, (\operatorname{Fintype}\left(A\right)) \Rightarrow\\{} (\operatorname{DecidableEq}\left(A\right)) \Rightarrow\\{} (\operatorname{Nonempty}\left(A\right)) \Rightarrow\\{} (\forall w: \operatorname{Block}\left(A\right) \to \mathbb{R}, \forall v: \operatorname{Block}\left(A\right) \to \mathbb{R}, (((\forall B: \operatorname{Block}\left(A\right), 0 \leq w\left(B\right)) \land\\{} (\forall B: \operatorname{Block}\left(A\right), 0 \leq v\left(B\right)) \land\\{} (\forall i: A, \sum_{{B: \operatorname{Block}\left(A\right)}} {\operatorname{row}\left(w, i, B\right)} = 1) \land\\{} (\forall i: A, \sum_{{B: \operatorname{Block}\left(A\right)}} {\operatorname{row}\left(v, i, B\right)} = 1))) \Rightarrow\\{} (\text{let }n = \operatorname{card}\left(A\right) \\{} M = (t: \mathbb{R} , u: \operatorname{Block}\left(A\right) \to \mathbb{R} , B: \operatorname{Block}\left(A\right) \mapsto (1 - t) \cdot \operatorname{ite}\left(\operatorname{card}\left(B\right) = 1, 1, 0\right) + t \cdot u\left(B\right)) \\{} Seed = \operatorname{Option}\left(\operatorname{Block}\left(A\right)\right) \times \operatorname{Option}\left(\operatorname{Block}\left(A\right)\right) \\{} E = (p: Seed \to \mathbb{R} , P: Seed \to \operatorname{Finpartition}\left(\operatorname{univ}\left(\right): \operatorname{Finset}\left(A\right)\right) , i: A , (r , B): Seed \times \operatorname{Block}\left(A\right) \mapsto \operatorname{ite}\left(\operatorname{part}\left(P\left(r\right), i\right) = B, p\left(r\right), 0\right))\\{}\text{in }((\forall t: \mathbb{R}, (0 \leq t) \Rightarrow\\{} (t \leq 1) \Rightarrow\\{} (((\operatorname{finiteDeficiency}\left(\operatorname{row}\left(M\left(t, v\right)\right), \operatorname{row}\left(M\left(t, w\right)\right)\right) = \operatorname{ofReal}\left(t\right) \cdot \operatorname{finiteDeficiency}\left(\operatorname{row}\left(v\right), \operatorname{row}\left(w\right)\right)) \land\\{} (\operatorname{finiteDeficiency}\left(\operatorname{row}\left(M\left(t, w\right)\right), \operatorname{row}\left(M\left(t, v\right)\right)\right) = \operatorname{ofReal}\left(t\right) \cdot \operatorname{finiteDeficiency}\left(\operatorname{row}\left(w\right), \operatorname{row}\left(v\right)\right))))) \land\\{} ((n = 1) \Rightarrow\\{} (((\operatorname{finiteDeficiency}\left(\operatorname{row}\left(v\right), \operatorname{row}\left(w\right)\right) = 0) \land\\{} (\operatorname{finiteDeficiency}\left(\operatorname{row}\left(w\right), \operatorname{row}\left(v\right)\right) = 0)))) \land\\{} ((2 \leq n) \Rightarrow\\{} (\forall t: \mathbb{R}, (0 \leq t) \Rightarrow\\{} (t \leq \frac{2}{n}) \Rightarrow\\{} (\exists p: Seed \to \mathbb{R}, \exists P: Seed \to \operatorname{Finpartition}\left(\operatorname{univ}\left(\right): \operatorname{Finset}\left(A\right)\right), \exists Q: Seed \to \operatorname{Finpartition}\left(\operatorname{univ}\left(\right): \operatorname{Finset}\left(A\right)\right), ((\forall r: Seed, 0 \leq p\left(r\right)) \land\\{} (\sum_{{r: Seed}} {p\left(r\right)} = 1) \land\\{} (\forall B: \operatorname{Block}\left(A\right), \sum_{{r: Seed}} {\operatorname{ite}\left(B \in \operatorname{parts}\left(P\left(r\right)\right), p\left(r\right), 0\right)} = M\left(t, w, B\right)) \land\\{} (\forall B: \operatorname{Block}\left(A\right), \sum_{{r: Seed}} {\operatorname{ite}\left(B \in \operatorname{parts}\left(Q\left(r\right)\right), p\left(r\right), 0\right)} = M\left(t, v, B\right)) \land\\{} (\exists F: \operatorname{FiniteMarkovKernel}\left(Seed \times \operatorname{Block}\left(A\right), \operatorname{Block}\left(A\right)\right), \exists R: \operatorname{FiniteMarkovKernel}\left(\operatorname{Block}\left(A\right), Seed \times \operatorname{Block}\left(A\right)\right), ((\forall i: A, \operatorname{channelOutput}\left(F.1, E\left(p, P, i\right)\right) = \operatorname{row}\left(M\left(t, w\right), i\right)) \land\\{} (\forall i: A, \operatorname{channelOutput}\left(R.1, \operatorname{row}\left(M\left(t, w\right), i\right)\right) = E\left(p, P, i\right)))) \land\\{} (\exists F: \operatorname{FiniteMarkovKernel}\left(Seed \times \operatorname{Block}\left(A\right), \operatorname{Block}\left(A\right)\right), \exists R: \operatorname{FiniteMarkovKernel}\left(\operatorname{Block}\left(A\right), Seed \times \operatorname{Block}\left(A\right)\right), ((\forall i: A, \operatorname{channelOutput}\left(F.1, E\left(p, Q, i\right)\right) = \operatorname{row}\left(M\left(t, v\right), i\right)) \land\\{} (\forall i: A, \operatorname{channelOutput}\left(R.1, \operatorname{row}\left(M\left(t, v\right), i\right)\right) = E\left(p, Q, i\right)))))))))))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/CARRevelationScaling.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is an arbitrary finite nonempty state type at any universe level u, with decidable equality, and n is its cardinality. Block(A) is the alphabet of all nonempty finite subsets of A. The profiles w and v take arbitrary nonnegative real values, and each CAR row sums to one. The row(u,i,B) equals u(B) if i belongs to B and zero otherwise. Singleton and zero-weight blocks remain in this alphabet.

finiteDeficiency takes the target first and the source second. It minimizes the maximum statewise half-L1 error over all stochastic kernels on the full alphabet. One kernel is used for every state; its output rows may assign mass to zero-weight target blocks and to blocks that do not contain the true state. No support restriction or prior is imposed on this minimization.

$$
\begin{gathered}\operatorname{finiteDeficiency}\left(Y, X\right) = \operatorname{iInf}\left((K: \operatorname{FiniteMarkovKernel}\left(\operatorname{Block}\left(A\right), \operatorname{Block}\left(A\right)\right) \mapsto \operatorname{ofReal}\left(\operatorname{max}\left(i, A, \frac{1}{2} \cdot \sum_{{B: \operatorname{Block}\left(A\right)}} {\lvert Y\left(i, B\right) - \operatorname{channelOutput}\left(K.1, X\left(i\right)\right)\left(B\right) \rvert}\right)\right))\right)\end{gathered}
$$

The function M mixes a profile with complete revelation: the revealing profile is one on every singleton and zero on every larger block. Both equalities hold for every real t between zero and one, with multiplication by ofReal(t) in the extended nonnegative reals. For n = 1 the only block is the unique singleton, both original profiles have weight one, and both original deficiencies vanish.

Finite Bayes minima are attained. For a probability prior mu, a finite nonempty action set D, and a loss l between zero and one, choose at each observation an action minimizing its finite sum of weighted losses. The resulting deterministic decision rule is stochastic and no randomized rule has a smaller cost. For a CAR profile u this choice separates block by block: H(B) is independent of u, including when u(B) is zero. Thus the same H applies to both profiles and their revealing mixtures.

$$
\begin{gathered}\operatorname{H}\left(B\right) = \operatorname{min}\left(a, D, \sum_{{i \in B}} {mu\left(i\right) \cdot l\left(i, a\right)}\right) \\{} \operatorname{toReal}\left(\operatorname{finiteBayesRisk}\left(mu, l, \operatorname{row}\left(u\right)\right)\right) = \sum_{{B: \operatorname{Block}\left(A\right)}} {u\left(B\right) \cdot \operatorname{H}\left(B\right)}\end{gathered}
$$

To obtain a shared optimizing kernel and task, take stochastic experiments X and Y on O = Block(A). The kernel domain is the finite product of probability simplexes, and the second domain is the probability simplex on A times Finset(O). The displayed payoff is continuous and affine in each variable. These nonempty compact convex domains admit an actual Sion saddle (Kstar,zstar). The saddle inequalities hold for every kernel K and every state-event probability vector z.

$$
\begin{gathered}\operatorname{f}\left(K, z\right) = \sum_{{i: A}} {\sum_{{S: \operatorname{Finset}\left(O\right)}} {z\left((i , S)\right) \cdot \sum_{{C \in S}} {\operatorname{channelOutput}\left(K.1, X\left(i\right)\right)\left(C\right) - Y\left(i, C\right)}}} \\{} \operatorname{f}\left(Kstar, z\right) \leq \operatorname{f}\left(Kstar, zstar\right) \\{} \operatorname{f}\left(Kstar, zstar\right) \leq \operatorname{f}\left(K, zstar\right)\end{gathered}
$$

Sum zstar over events to obtain the prior mu, and over events containing an output letter to obtain g. Then zero is at most g(i,C) and g(i,C) is at most mu(i). The loss is g(i,C)/mu(i) for positive mu(i), and zero when mu(i) is zero. In the latter case g(i,C) is also zero, so mu(i) l(i,C) = g(i,C) holds without discarding any state.

$$
\begin{gathered}mu\left(i\right) = \sum_{{S: \operatorname{Finset}\left(O\right)}} {zstar\left((i , S)\right)} \\{} g\left(i, C\right) = \sum_{{S: \operatorname{Finset}\left(O\right)}} {\operatorname{ite}\left(C \in S, zstar\left((i , S)\right), 0\right)} \\{} l\left(i, C\right) = \operatorname{ite}\left(mu\left(i\right) = 0, 0, \frac{g\left(i, C\right)}{mu\left(i\right)}\right) \\{} mu\left(i\right) \cdot l\left(i, C\right) = g\left(i, C\right)\end{gathered}
$$

The positive-difference event of each simulated row realizes its half-L1 distance from the target row. Testing the saddle against these events and an attained Bayes decision bounds every state error of Kstar by the same task's Bayes-risk gap. Bounded-loss risk transport gives the converse bound by deficiency, and the defining infimum bounds deficiency by the error of Kstar. All three values are equal. Probability rows bound deficiency by one, and the attained nonnegative Bayes costs are finite, so the conversions to real values in these formulas are valid.

$$
\begin{gathered}\operatorname{uniformSimulationError}\left(Y, X, Kstar\right) = \operatorname{toReal}\left(\operatorname{finiteDeficiency}\left(Y, X\right)\right) \\{} \operatorname{toReal}\left(\operatorname{finiteDeficiency}\left(Y, X\right)\right) = \operatorname{toReal}\left(\operatorname{finiteBayesRisk}\left(mu, l, X\right)\right) - \operatorname{toReal}\left(\operatorname{finiteBayesRisk}\left(mu, l, Y\right)\right)\end{gathered}
$$

For each fixed task, the complete-revelation contribution in the block risk formula is identical for w and v and cancels. Apply the attained task for the mixed experiments to bound their deficiency above by t times the original deficiency. Apply the attained task for the original experiments to the mixed ones to obtain the reverse inequality. Interchanging w and v proves the second directed equality. This argument includes t = 0 and never divides by t; no duality or attainment hypothesis is required.

$$
\begin{gathered}\operatorname{toReal}\left(\operatorname{finiteBayesRisk}\left(mu, l, \operatorname{row}\left(\operatorname{M}\left(t, w\right)\right)\right)\right) - \operatorname{toReal}\left(\operatorname{finiteBayesRisk}\left(mu, l, \operatorname{row}\left(\operatorname{M}\left(t, v\right)\right)\right)\right) = t \cdot (\operatorname{toReal}\left(\operatorname{finiteBayesRisk}\left(mu, l, \operatorname{row}\left(w\right)\right)\right) - \operatorname{toReal}\left(\operatorname{finiteBayesRisk}\left(mu, l, \operatorname{row}\left(v\right)\right)\right))\end{gathered}
$$

For the partition construction suppose n is at least two and 0 <= t <= 2/n, which also implies t <= 1. For either original profile u, let S(u) be the total weight of nonsingleton blocks. Summing the CAR row equations over states counts each block weight once per member. Nonnegativity and the size of each nonsingleton give S(u) <= n/2, hence t S(u) <= 1.

$$
\begin{gathered}\operatorname{S}\left(u\right) = \sum_{{B: \operatorname{Block}\left(A\right)}} {\operatorname{ite}\left(2 \leq \operatorname{card}\left(B\right), u\left(B\right), 0\right)} \\{} 2 \cdot \operatorname{S}\left(u\right) \leq \sum_{{B: \operatorname{Block}\left(A\right)}} {\operatorname{card}\left(B\right) \cdot u\left(B\right)} \\{} \sum_{{B: \operatorname{Block}\left(A\right)}} {\operatorname{card}\left(B\right) \cdot u\left(B\right)} = n \\{} \operatorname{S}\left(u\right) \leq \frac{n}{2} \\{} t \cdot \operatorname{S}\left(u\right) \leq 1\end{gathered}
$$

For every nonempty block B form the ordinary partition with B as one part and each state outside B as its own singleton part. These parts are nonempty, pairwise disjoint, and have union A. Let T(none) be the discrete partition and T(some(B)) this partition. The selector law q(u) gives mass t u(B) to some(B) when B is nonsingleton, zero to singleton selectors, and the residual mass 1 - t S(u) to none. All masses are nonnegative and their sum is one.

$$
\begin{gathered}\operatorname{T}\left(\operatorname{none}\left(\right)\right) = \operatorname{discrete}\left(A\right) \\{} \operatorname{parts}\left(\operatorname{T}\left(\operatorname{some}\left(B\right)\right)\right) = \operatorname{union}\left(\operatorname{singleton}\left(B\right), \{\operatorname{singleton}\left(i\right) \mid i \in A, \operatorname{not}\left(i \in B\right)\}\right) \\{} \operatorname{q}\left(u, \operatorname{none}\left(\right)\right) = 1 - t \cdot \operatorname{S}\left(u\right) \\{} \operatorname{q}\left(u, \operatorname{some}\left(B\right)\right) = \operatorname{ite}\left(2 \leq \operatorname{card}\left(B\right), t \cdot u\left(B\right), 0\right)\end{gathered}
$$

A nonsingleton block B occurs with total probability t u(B). A singleton {i} occurs under the discrete selector and under exactly those nonsingleton selectors whose block omits i. The CAR row equation gives its probability 1 - t + t u({i}). Thus the induced profile is exactly M(t,u) on every block.

$$
\begin{gathered}1 - t \cdot \operatorname{S}\left(u\right) + t \cdot \sum_{{B: \operatorname{Block}\left(A\right)}} {\operatorname{ite}\left((2 \leq \operatorname{card}\left(B\right) \land \operatorname{not}\left(i \in B\right)), u\left(B\right), 0\right)} = 1 - t + t \cdot u\left(\operatorname{singleton}\left(i\right)\right)\end{gathered}
$$

Use the actual product law of the two selector laws on Seed = Option(Block(A)) times Option(Block(A)). Define P from its first coordinate and Q from its second. The law is independent of the state, nonnegative, and of total mass one; its induced profiles are M(t,w) and M(t,v), respectively. Both experiments reveal the entire same seed r, together with the part containing the state. The common seed and the partition realizations are constructed, not assumed.

$$
\begin{gathered}\operatorname{p}\left((a , b)\right) = \operatorname{q}\left(w, a\right) \cdot \operatorname{q}\left(v, b\right) \\{} \operatorname{P}\left((a , b)\right) = \operatorname{T}\left(a\right) \\{} \operatorname{Q}\left((a , b)\right) = \operatorname{T}\left(b\right) \\{} \operatorname{E}\left(p, T, i, (r , B)\right) = \operatorname{ite}\left(\operatorname{part}\left(T\left(r\right), i\right) = B, \operatorname{p}\left(r\right), 0\right)\end{gathered}
$$

The experiment E(p,T) assigns p(r) to the output (r,B) precisely when B is the part of T(r) containing the state. For each of T = P and T = Q separately, let h be its induced profile, respectively M(t,w) and M(t,v). Forgetting the seed uses the deterministic kernel F((r,C),B) = indicator(C = B). For reconstruction, choose a fixed state iota and output ostar = ((none,none),{iota}) to complete each zero-weight input row. Positive-weight input rows condition the entire seed on the event that B is a part of T(r), while keeping the observed block.

$$
\begin{gathered}ostar = ((\operatorname{none}\left(\right) , \operatorname{none}\left(\right)) , \operatorname{singleton}\left(iota\right)) \\{} \operatorname{F}\left((r , C), B\right) = \operatorname{ite}\left(C = B, 1, 0\right) \\{} \operatorname{R}\left(B, (r , C)\right) = \operatorname{ite}\left(h\left(B\right) = 0, \operatorname{ite}\left(ostar = (r , C), 1, 0\right), \operatorname{ite}\left((B = C \land B \in \operatorname{parts}\left(T\left(r\right)\right)), \frac{\operatorname{p}\left(r\right)}{h\left(B\right)}, 0\right)\right)\end{gathered}
$$

The induced-profile equation makes each positive reconstruction row sum to one. If h(B) = 0 and B is a part of T(r), nonnegativity gives 0 <= p(r) <= h(B), hence p(r) = 0. This proves the reconstruction identity also on zero-weight blocks, while the fixed point mass makes those kernel rows stochastic. Finally, B is the part containing i exactly when B is a part and i belongs to B. This gives both exact channelOutput identities for P and both for Q. At t = 0 the product law concentrates on (none,none), so the same construction covers complete revelation without a positive-t assumption.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/CARRevelationScaling.result`
- Dependency: [D5/S3/Estimation/DecisionRisk/CARApproximateRecovery](CARApproximateRecovery.md)
