# Quantized Word Approximation

## Abstract

Supplied quantizers give finite-state predictions for every action word.

Let X and Y be arbitrary metric spaces and A an arbitrary action alphabet. For every a in A, the total map F_a:X->X satisfies d_X(F_a(x),F_a(y)) <= L d_X(x,y), where L >= 0. The observation o:X->Y satisfies d_Y(o(x),o(y)) <= M d_X(x,y), where M >= 0.

Given a natural s, centers z:Fin(s)->X, a map Q:X->Fin(s), and a real delta, assume d_X(x,z(Q(x))) <= delta for every x. The finite machine initializes at Q(x), updates i to Q(F_a(z(i))), and reads o(z(i)). Its transition and readout maps are quantizedUpdate and quantizedReadout.

**Theorem 1.1 (Finite-word and uniform contraction bounds).**

$$\begin{gathered}\forall x\in X, \forall w\in A^{*}, t=length(w)\\d_{Y}(o(F_{w}(x)), o(z(G_{w}(Q(x)))))\leq M\Delta\sum_{j=0}^{t}L^{j},\\L<1\Rightarrow d_{Y}(o(F_{w}(x)), o(z(G_{w}(Q(x)))))\leq\frac{M\Delta}{1-L}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.quantized_word_approximation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every x in X and every finite word w of length t, the output error is at most M delta times the sum of L^j for j=0,...,t. If L<1, the error of this same machine is at most M delta/(1-L), for every initial state and every word.

Both trajectories use ControlledBehaviorUniversality.runWord: an action at the head of a list is executed first. Thus F_(uv)=F_v composed with F_u. The word may be empty, in which case the error is at most M delta.

For an arbitrary stored label i, induction on w proves d_X(F_w(y),z(G_w(i))) <= L^t d_X(y,z(i)) + delta sum_(j<t) L^j. The successor estimate uses the actual intermediate state F_a(z(i)): the triangle inequality, the common Lipschitz bound, and the supplied quantizer inequality give d_X(F_a(y),z(Q(F_a(z(i))))) <= L d_X(y,z(i)) + delta. This estimate is propagated along the entire remaining word.

Set i=Q(x) and apply its quantizer bound to the initial discrepancy. The geometric sum then includes exponent t. Applying the observation bound gives the output estimate. Under L<1, Mathlib's geom_sum_mul_neg and L^(t+1)>=0 bound the finite sum by 1/(1-L). For each actual input x, nonnegativity of delta follows from 0<=d_X(x,z(Q(x)))<=delta.

No independent Nonempty X, positive state count, or nonnegative delta hypothesis is needed. If X is empty, the conclusion quantified over x is vacuous; a map Q into Fin(0) forces that case. Empty alphabets leave only the empty word. The same formulas include L=0, M=0, delta=0, and t=0 without division by L or M. The statement also applies when A is infinite; finite alphabets are a special case.

This is a mathematical construction from the supplied maps. Effective evaluation of Q(F_a(z(i))) and o(z(i)) is a separate condition for executable transition and output tables. The result does not assert that arbitrary covers are update-consistent, nor that Q or the source dynamics are computable.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/QuantizedWordApproximation.quantized_word_approximation`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](ControlledBehaviorUniversality.md)
