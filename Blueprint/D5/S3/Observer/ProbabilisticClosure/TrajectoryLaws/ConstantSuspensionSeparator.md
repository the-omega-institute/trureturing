# Constant suspended emission separates complete endpoint laws

## Abstract

A finite stationary generator with constant suspended emission cannot simultaneously center both endpoint complete laws within excess one over 35200.

RegularTable quantifies over arbitrary finite carriers X and Y, nonnegative stochastic update tables B:X to Y and A:Y to X, and probability rows pi and tau satisfying pi B=tau and tau A=pi. The emission probabilities u on X and v on Y lie in the closed interval [1/3,2/5]. No positive-entry, irreducibility, aperiodicity, independence or reversibility condition is imposed.

The output carrier is the existing RawTail=Option(List(Letter)), with Letter=Fin(2), alpha=0 and beta=1. None remains an outcome for noncompletion. Each Q(x) and W(y) is a normalized measure on the entire carrier. The table requires exact same-update recursion for every set E: Q(x)(E) equals u(x) times the indicator that [alpha] belongs to E, plus (1-u(x)) times the B(x,.) average of W evaluated on the beta-prefix preimage of E. The W recursion has immediate [beta] mass 1-v(y), followed by v(y) times the A(y,.) average of Q on the alpha-prefix preimage. Prefixing fixes none. No law is conditioned on completion.

Write Qbar and Wbar for the pi and tau averages. FullTVBound(mean,P,radius) means that the absolute difference between mean(E) and P(E) is at most radius for every complete event E. This is the event-supremum total variation convention. P is the existing Bernoulli stopped-word law, identified with the actual first-completion process by `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw`.

In the displayed theorem, ep and eb denote epsilon_p and epsilon_beta, and inRegularInterval(s) means 1/3<=s<=2/5. constantOnPositiveSupport(R,s) means v(y)=s whenever tau(y)>0; values at zero-weight labels need not equal s. completeEndpointBounds requires FullTVBound for Qbar against both p endpoint laws, each with radius 1116529/22781250+epsilon_p, and for Wbar against both beta endpoint laws, each with radius 239/6750+epsilon_beta. The two endpoint alpha probabilities are exactly 1/3 and 2/5.

**Theorem 1.1 (Uniform strict separation over every finite regular table).**

$$\forall X \in FiniteType,\; \forall Y \in FiniteType,\; \forall R \in \operatorname{RegularTable}\left(X, Y\right),\; \forall s \in Real,\; \forall ep \in Real,\; \forall eb \in Real,\; (\operatorname{inRegularInterval}\left(s\right)\land\operatorname{constantOnPositiveSupport}\left(R, s\right)\land0\le ep\land0\le eb\land\operatorname{completeEndpointBounds}\left(R, ep, eb\right))\Rightarrow\frac{1}{35200}<\operatorname{max}\left(ep, eb\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ConstantSuspensionSeparator.constant_suspension_separator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The acquired return table C=BA has stationary row pi. With U=1-u, one four-coordinate probability distribution has mass pi(i)C(i,j)C(j,k)C(k,l). Every coordinate has marginal pi. Positive-weight rows have no positive transition into a zero-weight row. This support fact permits the suspended constancy hypothesis to be used exactly where the recursion has positive weight.

Let m be the common mean of U and M_j the product expectation of the first j coordinates of that one distribution. The full law recursions give Qbar(pWord(j,1))=(1-s)s^j M_(j+1) for j=0,1,2,3, and Wbar(E_beta)=1-s+s(1-s)m for E_beta={[beta],alpha::pWord(0,1)}. The proof first establishes the word recursion for arbitrary natural j and the complete-event identity Wbar=(1-s)delta_beta+s alpha-prefix(Qbar). The suspended event and all four words therefore refer to the same table and the same m.

The consumed product bounds are M_2<=(19/15)m-2/5, M_3<=(271/225)m-38/75 and M_4>=(4/15)(4m-29/15). They are classical box-envelope instances described in `D5/L/Analytic/xu2020polyhedral`. Their finite proofs use polynomial nonnegativity inside the live derivation; no claim is made that their separate equality cases can be attained together.

Apply the full endpoint bounds to E_p={pWord(0,1),pWord(1,1),pWord(2,1)}, E_beta, and E_p union {pWord(3,1)}. Exact endpoint masses yield the two midpoint errors and Qbar(pWord(3,1))<=1944/390625+2 epsilon_p. The last bound follows by subtracting the E_p lower bound from the larger event's upper bound. It does not replace the full-law hypothesis by a finite-probe hypothesis.

Set c=1489/6750. The same-law estimates imply Cp-F(s)<=epsilon_p+5 epsilon_beta and G(s)-1944/390625<=2 epsilon_p+epsilon_beta/5, where Cp=11758471/22781250, F(s)=(1-c/s)(1+19s/15+271s^2/225)-(2/5)s(1-s)(1+19s/15), and G(s)=(4/15)(31s^3/15+29s^4/15-4cs^2). Both functions increase on the regular interval. At s=3679/10000 their respective strict gaps exceed 1/4000 and 1/16000. The two exhaustive sides of this cut imply the displayed strict lower bound.

This theorem concerns the stated regular finite table and its complete laws. It does not establish extraction of such a table from every original history, an isomorphism with the full record and event transcript, or the clipping comparison for arbitrary original emissions. Those bridges are required before an original-observer lower bound of 1/195200 can be asserted. The reduction also makes no resource-preservation claim.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ConstantSuspensionSeparator.constant_suspension_separator`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw](FourthSegmentStoppedLaw.md)
- Narrative reference: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentStoppedLaw](FourthSegmentStoppedLaw.md)
