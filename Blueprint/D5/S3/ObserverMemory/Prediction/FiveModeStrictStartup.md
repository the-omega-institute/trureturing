# Five Mode Strict Startup and Initialized Count

## Abstract

Strict startup nonrecurrence strengthens the initialized lower bound for the unrestricted five-mode generated observer.

Use the unchanged passive five-mode source with positive p,q,r and p+q+r<1. Its holding probabilities are a=1-p-q and b=1-r, with a different from b. The visible alphabet is Fin 4 in Lean order 0,1,B,3, B=2. The minority coordinate at startup index k is delta(k)=theta^k/(1+theta^k), theta=min(a,b)/max(a,b). Every finite startup history B^(k+1) has positive actual probability. startup(O,k) is the configuration obtained by the actual fold of the one total update on that history.

A GeneratedObserver on Z has initialization, a total deterministic update, and normalized nonnegative emission rows everywhere. Its decoded law is generatedLaw using those same rows and that same update at every hypothetical symbol. Zero forecast probabilities do not remove actual legal updates. All configurations of the finite carrier count, including initialization and configurations used only by generated words. A hidden source mode is a proof coordinate, without supplying an extra observer input.

Accurate(O,p,q,r,epsilon,true) quantifies every positive finite actual history including the empty history and every natural future horizon. At the empty history the source future begins with Y0; after a nonempty acquired history it begins with the next source step. Guarantee below is the original equivalent formulation restricted to positive horizons; the original guarantee_accurate supplier extends it to horizon zero by normalization. No positive actual history, however rare, is discarded.

**Theorem 1.1 (startup collision strict).**

$$\forall Z \in \operatorname{Type}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall j \in \operatorname{Nat}\left(\right),\; \left(\left(\left(\left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \land \operatorname{Accurate}\left(\operatorname{toObserver}\left(O\right), p, q, r, \mathit{epsilon}, \operatorname{true}\left(\right)\right)\right) \land i < j\right) \land \operatorname{startupState}\left(\operatorname{toObserver}\left(O\right), i\right) = \operatorname{startupState}\left(\operatorname{toObserver}\left(O\right), j\right)\right) \Rightarrow \operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), i\right) < 2 \cdot \mathit{epsilon}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.startup_collision_strict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A collision gives a positive B period. The existing nonstrict collision theorem bounds delta(i) by 2*epsilon. At equality the recurring decoder is within epsilon of both the dominant pure law and the startup law at index i. FiveModePeriodicDiameter.periodic_diameter_obstruction excludes that equality. This strict theorem itself requires no small-error hypothesis beyond its complete accuracy assumption.

**Definition 1.2 (J).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; \operatorname{J}\left(p, q, r, \mathit{epsilon}\right) = \operatorname{ifThenElse}\left(\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), \operatorname{N2}\left(p, q, r, \mathit{epsilon}\right)\right) = 2 \cdot \mathit{epsilon}, \operatorname{N2}\left(p, q, r, \mathit{epsilon}\right) + 1, \operatorname{N2}\left(p, q, r, \mathit{epsilon}\right)\right)$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N2 is the first nonstrict delta(k)<=2*epsilon cutoff. In the unequal small-error domain, J is the first strict delta(k)<2*epsilon cutoff: J>0, delta(J)<2*epsilon, and every i<J has delta(i)>=2*epsilon. Hence J=N2 away from equality and J=N2+1 at equality, with N2<=J<=N1.

**Theorem 1.3 (startup never recurs before J).**

$$\forall Z \in \operatorname{Type}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; \forall i \in \operatorname{Nat}\left(\right),\; \forall j \in \operatorname{Nat}\left(\right),\; \left(\left(\left(\left(\left(\left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \land 0 < 2 \cdot \mathit{epsilon}\right) \land 2 \cdot \mathit{epsilon} < \operatorname{kappa}\left(p, q, r\right)\right) \land \operatorname{Accurate}\left(\operatorname{toObserver}\left(O\right), p, q, r, \mathit{epsilon}, \operatorname{true}\left(\right)\right)\right) \land i < \operatorname{J}\left(p, q, r, \mathit{epsilon}\right)\right) \land i < j\right) \Rightarrow \operatorname{startupState}\left(\operatorname{toObserver}\left(O\right), i\right) \ne \operatorname{startupState}\left(\operatorname{toObserver}\left(O\right), j\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.startup_never_recurs_before_J` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The later index j is unrestricted above. This is stronger than pairwise distinctness of a finite initial segment.

**Theorem 1.4 (generated initialized lower).**

$$\forall Z \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(Z\right)] \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; \left(\left(\left(\left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \land 0 < 2 \cdot \mathit{epsilon}\right) \land 2 \cdot \mathit{epsilon} < \operatorname{kappa}\left(p, q, r\right)\right) \land \left(\forall h \in \operatorname{List}\left(\operatorname{Visible}\left(\right)\right),\; 0 < \operatorname{historyMass}\left(p, q, r, h\right) \Rightarrow \left(\forall H \in \operatorname{Nat}\left(\right),\; 0 < H \Rightarrow \operatorname{totalVariation}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, h, H\right), \operatorname{generatedLaw}\left(\operatorname{update}\left(O\right), \operatorname{row}\left(O\right), \operatorname{run}\left(\operatorname{toObserver}\left(O\right), h\right), H\right)\right) \le \mathit{epsilon}\right)\right)\right) \Rightarrow 6 + \operatorname{min}\left(\operatorname{N1}\left(p, q, r, \mathit{epsilon}\right), \operatorname{J}\left(p, q, r, \mathit{epsilon}\right) + 1\right) \le \operatorname{card}\left(Z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.generated_initialized_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The lower bound uses the entire finite carrier. Select the five actually reached, exact pure-law configurations supplied by recurrent_pair_rigidity. For each k<N1, the startup profile is more than epsilon from every one of those exact pure laws: the dominant distance is delta(k), the other ambiguous distance is 1-delta(k)>=1/2, and singleton separation is at least kappa. The original postread_initialization_extra_state supplier separates initialization from each reached selection and startup configuration.

Put M=min(N1,J+1). The exact pure selections and the first M startup configurations give a disjoint injection from State plus Fin M into Z. If two startup indices in that segment differ, the smaller is strictly below J, so the strict nonrecurrence theorem separates them, including the possible additional index J. Adding initialization gives an injection from Option(State plus Fin M), whose cardinality is 6+M. No assertion removes generated-only configurations or assumes a unique synchronized recurrent presentation.

**Theorem 1.5 (initialized generated strict minimum).**

$$\forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; \left(\left(\left(\operatorname{admissible}\left(p, q, r\right) \land \operatorname{a}\left(p, q\right) \ne \operatorname{b}\left(r\right)\right) \land 0 < 2 \cdot \mathit{epsilon}\right) \land 2 \cdot \mathit{epsilon} < \operatorname{kappa}\left(p, q, r\right)\right) \Rightarrow \left(\left(\left(\left(\left(\forall n \in \operatorname{Nat}\left(\right),\; \operatorname{Attainable}\left(p, q, r, \mathit{epsilon}, n\right) \Rightarrow 6 + \operatorname{min}\left(\operatorname{N1}\left(p, q, r, \mathit{epsilon}\right), \operatorname{J}\left(p, q, r, \mathit{epsilon}\right) + 1\right) \le n\right) \land 6 + \operatorname{min}\left(\operatorname{N1}\left(p, q, r, \mathit{epsilon}\right), \operatorname{J}\left(p, q, r, \mathit{epsilon}\right) + 1\right) \le \operatorname{minimum}\left(\operatorname{admissibilityProof}\left(p, q, r\right), \operatorname{unequalProof}\left(p, q, r\right), \operatorname{positiveErrorProof}\left(\mathit{epsilon}\right), \operatorname{smallErrorProof}\left(p, q, r, \mathit{epsilon}\right)\right)\right) \land \operatorname{minimum}\left(\operatorname{admissibilityProof}\left(p, q, r\right), \operatorname{unequalProof}\left(p, q, r\right), \operatorname{positiveErrorProof}\left(\mathit{epsilon}\right), \operatorname{smallErrorProof}\left(p, q, r, \mathit{epsilon}\right)\right) \le 6 + \operatorname{N1}\left(p, q, r, \mathit{epsilon}\right)\right) \land \left(\operatorname{N2}\left(p, q, r, \mathit{epsilon}\right) < \operatorname{N1}\left(p, q, r, \mathit{epsilon}\right) \Rightarrow 7 + \operatorname{N2}\left(p, q, r, \mathit{epsilon}\right) \le \operatorname{minimum}\left(\operatorname{admissibilityProof}\left(p, q, r\right), \operatorname{unequalProof}\left(p, q, r\right), \operatorname{positiveErrorProof}\left(\mathit{epsilon}\right), \operatorname{smallErrorProof}\left(p, q, r, \mathit{epsilon}\right)\right)\right)\right) \land \left(\operatorname{minority}\left(\operatorname{theta}\left(p, q, r\right), \operatorname{N2}\left(p, q, r, \mathit{epsilon}\right)\right) = 2 \cdot \mathit{epsilon} \Rightarrow \left(\operatorname{N2}\left(p, q, r, \mathit{epsilon}\right) + 2 \le \operatorname{N1}\left(p, q, r, \mathit{epsilon}\right) \Rightarrow 8 + \operatorname{N2}\left(p, q, r, \mathit{epsilon}\right) \le \operatorname{minimum}\left(\operatorname{admissibilityProof}\left(p, q, r\right), \operatorname{unequalProof}\left(p, q, r\right), \operatorname{positiveErrorProof}\left(\mathit{epsilon}\right), \operatorname{smallErrorProof}\left(p, q, r, \mathit{epsilon}\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.initialized_generated_strict_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Attainable is the existing existence predicate for accurate GeneratedObserver(Fin n), and Minimum denotes its existing attained minimum with the displayed admissibility and error hypotheses. Applying the carrier lower bound to every attainable n and to minimum_attained yields these conclusions. The existing source-exact truncation construction still gives the upper bound 6+N1. The result supplies a lower bound, not a complete unrestricted minimization theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.J`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.generated_initialized_lower`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.initialized_generated_strict_minimum`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.startup_collision_strict`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup.startup_never_recurs_before_J`
- Dependency: [D5/S3/ObserverMemory/Prediction/FiveModePeriodicDiameter](FiveModePeriodicDiameter.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity](FiveModeRecurrentPairRigidity.md)
