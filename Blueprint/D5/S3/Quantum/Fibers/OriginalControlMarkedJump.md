# Original Continuous Marked Jump Law

## Abstract

The original double-wall jump operators determine a normalized continuous marked law on each affine leg.

**Theorem 1.1 (A complete marked probability law on an affine leg).**

$$\begin{gathered}\forall L:Leg, chi,beta:\mathbb{R}, m:\mathbb{Z}, theta:\operatorname{Fin}(5)\to \mathbb{R},\\{}\operatorname{OC}(\operatorname{base}(L),\operatorname{duration}(L),\operatorname{height}(L),\operatorname{const}(chi))\land \operatorname{AC}(\operatorname{height}(L),0,\operatorname{duration}(L))\land \operatorname{FC}(\operatorname{duration}(L),\operatorname{height}(L),\operatorname{const}(chi))\land \\{}(\forall t:\mathbb{R}, i:\operatorname{Fin}(5),\operatorname{H}(L,chi,t,i)=0)\land \\{}(\forall i:\operatorname{Fin}(5), t:\mathbb{R},\operatorname{modeMeasure}(L,i)(\operatorname{singleton}(t))=0)\land (\forall i:\operatorname{Fin}(5),\operatorname{modeMeasure}(L,i)(\operatorname{Ioc}(0,\operatorname{duration}(L))^{c})=0)\land \\{}(\forall t\in \operatorname{Icc}(0,\operatorname{duration}(L)),\operatorname{survival}(L,t)=\operatorname{If}(\operatorname{x}(L)\leq \operatorname{y}(L),\frac{\operatorname{x}(L)}{\operatorname{height}(L)(t)},\frac{\operatorname{c}(L)-\operatorname{x}(L)}{\operatorname{c}(L)-\operatorname{height}(L)(t)}))\land \operatorname{IsProbabilityMeasure}(\operatorname{markedLaw}(L))\land \\{}(\forall E:\operatorname{Set}(Record),\operatorname{MeasurableSet}(E)\Rightarrow \operatorname{markedLaw}(L)(E)=\operatorname{If}(s\in E,\operatorname{ofReal}(\operatorname{SuccessMass}(L,beta,m,theta)),0)+\sum_{i: \operatorname{Fin}(5)} \operatorname{lintegral}(\operatorname{FailureSection}(L,E,i),t\mapsto \operatorname{ofReal}(\operatorname{JumpMass}(L,beta,m,theta,t,i))))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/OriginalControlMarkedJump.affine_marked_probability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix c below one half and positive heights x,y below c. A positive duration h gives the actual height k(t)=x+(y-x)*t/h. The five probabilities are (k,c-k,1-2*c,c-k,k), with the last coordinate retaining original mode13. Both directions and the stationary case are included. A constant real control phase has zero transported phase. No common duration or speed bound is imposed.

In the displayed statement h, k, c, x and y are duration(L), height(L), c(L), x(L) and y(L); base(L)=(c,c,1-2*c), S(t)=survival(L,t), mu=markedLaw(L), and nu(i)=modeMeasure(L,i). A set superscript c denotes its complement. OC, AC and FC mean OriginalControl, AbsolutelyContinuousOnInterval and FiniteC1Control, with exactly the displayed arguments. Record is Unit plus Fin5 times the real line; s is Sum.inl(). Its success singleton and all five time-labelled failure components are measurable.

H(L,chi,t,i) is the integral from zero to t of phaseWeight(base(L),k(u),i) times the derivative at u of the constant function chi. SuccessMass(L,beta,m,theta) is the sum over i:Fin5 of normSq of component i of successfulKraus(c,x,y,S(h)) applied to source(c,x,beta,m,theta). JumpMass(L,beta,m,theta,t,i) is normSq of component0 of jumpKraus(c,x,k(t),S(t),jumpRate(L,t),i) applied to that same source. FailureSection(L,E,i) is (0,h] intersected with the set of all t for which Sum.inr(i,t) belongs to E. lintegral(A,f) below uses Lebesgue measure restricted to A; ofReal is ENNReal.ofReal. These abbreviations retain exactly the successful vector and the absorbing row of the original operators.

The prepared input has middle amplitude sqrt(1-2*c). Each bottom amplitude is its positive probability square root times the negative exponential of its preparation angle plus an arbitrary common unknown phase. The two minus modes also carry the arbitrary integer parity factor. Thus every input of the original phase and parity family is retained, and its diagonal is exactly the original probability vector at x.

The actual hazard is the positive part of k prime divided by k, plus the positive part of minus k prime divided by c-k. Survival is defined by the exponential of minus the integral of this hazard. Integrating the appropriate logarithmic derivative gives x/k on an increasing leg, and (c-x)/(c-k) on a decreasing leg. The original mode jump rate is the hazard minus the derivative of log p_i(k). All five rates are nonnegative.

The successful operator is the original diagonal matrix with entries sqrt(S)*sqrt(p_i(k)/p_i(x)). The jump matrix is the absorbing row sqrt(g_i)*bra(i), multiplied by that successful matrix. Matrix action on the original prepared input gives squared absorbing amplitude g_i*S*p_i(k). Preparation phases cancel in this calculation; they are not chosen to simplify the input. The sum of the successful squared amplitudes is S.

Differentiating S*p_i(k) on a leg gives minus this mode density. Its integral is therefore p_i(x)-S(h)*p_i(y). Summing the five exact balances proves that the continuous failure mass is 1-S(h). The marked measure is the success atom of mass S(h), plus one density measure for every original mode on the entire continuous interval (0,h]. These measures have no failure atoms. Their total mass is one.

For every Borel set of records, the measure agrees with the sum of the actual squared Kraus outputs integrated over precisely its retained time and mode labels. The output space includes both terminal success and the complete continuous failure record. This is a finite-dimensional source-family statement. It makes no assertion about trace distance for arbitrary references or the common absorbing extension.

A repeated-prefix early and late construction additionally requires chronological assembly of these laws, equality of the literal common prefix on [0,1] in the duration2 controls, the exact suffix clocks, disjoint suffix failure supports, the event supremum in the probability convention of total variation, and the fixed positive height gap. Those conclusions, their resource equalities and the inverse obstruction do not follow merely from the affine-leg statement.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/OriginalControlMarkedJump.affine_marked_probability`
- Dependency: [D5/S3/Quantum/Fibers/OriginalControlComposition](OriginalControlComposition.md)
