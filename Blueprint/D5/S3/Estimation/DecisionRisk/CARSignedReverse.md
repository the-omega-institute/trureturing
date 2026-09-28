# Signed reverse deficiency for three-state CAR profiles

## Abstract

For arbitrary three-state CAR profiles, signed pair differences and forward deficiency bound reverse deficiency with coefficient three halves.

Let A = Fin 3, with states 0, 1 and 2. The alphabet O is `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.Block` applied to A: all seven nonempty subsets, including blocks of zero weight. For every real profile u on O, every state i and every block B, `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.row` is given by $\operatorname{row}(u, i, B) = \begin{cases}u(B)&i \in B\\0&\text{otherwise}\end{cases}$. For every pair of states i,j, `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.pair` is given by $\operatorname{pair}(u, i, j) = \sum_{{B: O}} {\begin{cases}u(B)&((i \in B) \land (j \in B))\\0&\text{otherwise}\end{cases}}$. These are the same CAR rows and pair weights in both directions.

`D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.finiteDeficiency` takes the target experiment first and the source experiment second. For experiments X,Y on O, finiteDeficiency(Y,X) is the infimum over all kernels K:O to O of ENNReal.ofReal(max_i TV(X_i K,Y_i)). Every K has nonnegative real entries and each row sums to one; the same K acts at every state. Here (X_i K)(C) = sum_B X_i(B) K(B,C) and TV(p,q) = (1/2) sum_C |p(C)-q(C)|. The optimization includes kernels sending mass to zero-weight target blocks or blocks not containing the true state, and includes arbitrary probability rows at unused source blocks.

**Theorem 1.1 (The three-halves reverse bound).**

$$\begin{gathered}A = \operatorname{Fin}(3), O = \operatorname{Block}(A)\\{}\forall w: O \to \mathbb{R}, v: O \to \mathbb{R},\\{}((\forall B: O, 0 \leq w(B)) \land (\forall B: O, 0 \leq v(B)) \land (\forall i: A, \sum_{{B: O}} {\operatorname{row}(w, i, B)} = 1) \land (\forall i: A, \sum_{{B: O}} {\operatorname{row}(v, i, B)} = 1)) \Rightarrow\\{}\text{let} \Delta = i j \mapsto (\operatorname{pair}(v, i, j)) - (\operatorname{pair}(w, i, j)),\\{}R = (\frac{1}{2}) \cdot (\max_{{i: A}} {\sum_{{j: A, j \neq i}} {\operatorname{max}(\Delta(i, j), 0)}})\\{}\text{in} \operatorname{finiteDeficiency}(\operatorname{row}(w), \operatorname{row}(v)) \leq \operatorname{ofReal}(\operatorname{min}(1, (R) + ((\frac{3}{2}) \cdot (\operatorname{toReal}(\operatorname{finiteDeficiency}(\operatorname{row}(v), \operatorname{row}(w))))))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DecisionRisk/CARSignedReverse.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both profiles range over arbitrary real weights on all seven blocks. The four hypotheses assert nonnegative weights and unit CAR row sums for each profile. Delta(i,j) is pair(v,i,j) minus pair(w,i,j), with its sign retained. R is one half of the largest incident sum of positive parts. The theorem assumes no common sign, permutation symmetry, positive weights, support restriction or risk-duality premise.

Write epsilon = toReal(finiteDeficiency(row(v),row(w))) for the forward deficiency from w to v. The left side is the reverse deficiency from v to w. Both deficiencies are at most one, so the forward value is finite and its conversion to a real number loses no information. The right side first takes the real minimum of one and R + (3/2) epsilon, then applies ENNReal.ofReal. This is an upper bound, not an exact formula for every profile pair.

For a finite nonempty action set D, a probability prior p and losses l(i,d) between zero and one, `D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.finiteBayesRisk` attains its infimum. For each observed letter x, choose an action minimizing sum_i p(i) X_i(x) l(i,d), and put unit decision mass on that action. Every stochastic decision row is a convex combination of these action costs and hence has no smaller cost. Thus the Bayes risk is ENNReal.ofReal(sum_x min_d sum_i p(i) X_i(x) l(i,d)). The same argument gives, for a nonnegative CAR profile u, the block formula sum_B u(B) H(B), where H(S) = min_d sum_{i in S} p(i) l(i,d).

To pass from bounded tasks to a common kernel, apply Sion's saddle point theorem to the product of kernel row simplexes and the simplex on state-event pairs (i,E), with E any subset of O. The payoff is sum_{i,E} z(i,E) sum_{b in E} ((X_i K)(b)-Y_i(b)). Both sets are nonempty, compact and convex, and the payoff is continuous and affine in each variable. At the saddle point, set p(i) = sum_E z(i,E) and g(i,b) = sum_{E containing b} z(i,E). Then 0 <= g(i,b) <= p(i). Set l(i,b) = g(i,b)/p(i) for positive p(i), and zero otherwise; this preserves p(i) l(i,b) = g(i,b).

For each state, choose the event where X_i K - Y_i is nonnegative. Equal total masses identify its sum with half-L1 total variation. The saddle inequalities bound every state's error by the same payoff evaluated at an optimal decision for X. This payoff is the optimal cost for X minus the identity-decision cost for Y, which is at most the Bayes-risk difference. Consequently a single bounded task has source-minus-target risk at least the deficiency. The loss uses O as its finite action set. Zero priors and zero experiment entries remain included throughout.

Now fix one bounded task and subtract H({i}) from each weighted loss p(i) l(i,d), obtaining x(i,d). Each x(i,d) lies between zero and p(i), and each state has an action with x(i,d)=0. Put N(S)=H(S)-sum_{i in S} H({i}); it is the minimum of the sums of these same x(i,d). Define a(ij)=N({i,j}), s=a(01)+a(02)+a(12), h=N(A) and k=s-h. Attainment yields 0 <= a(ij) <= min(p(i),p(j)), s <= 1, s <= 2h and h <= a(ij)+p(t) for the remaining state t. All of these quantities belong to the same task and prior.

Let tau=v(A)-w(A), delta(ij)=Delta(i,j), and T=delta(01)+delta(02)+delta(12). The CAR row equations cancel the singleton centers in the risk difference. Since pair(u,i,j)=u({i,j})+u(A) for distinct states, the exact identity for the reverse risk difference is G=Risk_v-Risk_w=sum_{i<j} delta(ij) a(ij)-tau k.

`D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.deficiency_risk_bound` bounds every forward task difference by epsilon. Two uniform-prior tasks therefore give -tau/3 <= epsilon and tau/2-T/3 <= epsilon. The first has three actions with loss one only at the action's matching state: its pair minima are zero and its full-set minimum is one third. The second has three identification actions with zero correct loss and unit incorrect loss, together with an action of constant loss one half. Its pair minima are one third and its full-set minimum is one half.

For coefficients 0 <= c(ij) <= 1/2 with sum_{i<j} c(ij) <= 1, the signed sum sum_{i<j} delta(ij)c(ij) is at most R. Replace only negative edge coefficients by zero for an upper estimate; the two largest positive parts can each receive at most one half. Any two edges of a triangle share a state, so their half-sum is bounded by that state's incident positive sum divided by two. This also covers one or no positive edges.

If k >= 0, then k <= 1/2 and the coefficients a lie in this polytope. The first forward task gives G <= R + 3k epsilon <= R + (3/2) epsilon. If k < 0, put q=-k=h-s. The same task inequalities give 3q+2s <= 1, a(ij)+q <= 1/2 and q <= 1/3. Hence c(ij)=a(ij)+2q/3 lies in the polytope, and G=sum_{i<j} delta(ij)c(ij)+2q(tau/2-T/3) <= R+2q epsilon <= R+(2/3) epsilon <= R+(3/2) epsilon. The signed components are retained in both identities.

Apply the Sion task to source row(v) and target row(w), then use the bound valid for every bounded task. This proves the untruncated reverse deficiency bound. Total variation between probability rows is at most one, giving the displayed minimum.

## References

- Truth anchor: `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.Block`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.pair`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.row`
- Truth anchor: `D5/S3/Estimation/DecisionRisk/CARSignedReverse.result`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.deficiency_risk_bound`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.finiteBayesRisk`
- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.finiteDeficiency`
- Dependency: [D5/S3/Estimation/DecisionRisk/CARApproximateRecovery](CARApproximateRecovery.md)
