# Five Mode Recurrent Pair Rigidity

## Abstract

Every recurrent class of the actual synchronized source-observer chain has exact emissions and complete generated future laws.

The passive source has modes State=Fin 5, visible alphabet Visible=Fin 4, B=2, and the fixed transition matrix and uniform initialized law of FiniteStartFiveModeSource. Admissibility means p,q,r>0 and p+q+r<1. Both p=q and r=p+q are included. The visible rows in Lean order (0,1,B,3) are (c,p,r,q), (q,a,p,0), (0,q,a,p), (p,0,q,a), (r,0,b,0), with a=1-p-q, b=1-r and c=1-p-q-r.

A GeneratedObserver on the whole finite carrier Z has an initial configuration, arbitrary total update, and a normalized nonnegative emission row at every configuration. Its retained run folds that same update over actual observations; its generatedLaw multiplies the emissions along the same update on every hypothetical word. All generated-only configurations remain in Z. Forecast-zero actual-legal inputs remain defined. A source mode in a pair is a proof coordinate and supplies no observer input.

History means a finite chronological visible list. historyMass is its actual initialized cylinder mass. The empty query starts at Y0. A nonempty history of length n predicts Yn onward by the conditional acquired posterior. Words(H) is the entire function carrier Fin H to Visible, and finite TV is half the sum of absolute differences over that entire carrier. Thus impossible and zero-weight words are included. The theorem assumes the original guarantee only for positive natural H and arbitrary real epsilon<1. It derives epsilon>=0 from the guarantee and extends it to H=0 using normalization; no error-sign premise is added.

Synchronized(p,q,r,O,t) is witnessed by a positive actual history containing a symbol other than B, with sourceRun pure at mode(t) and the retained run equal to configuration(t). The acquired positive-history invariant identifies its actual posterior with the pure source vector. Every singleton-containing actual history has such a pure source tag. The symbol update nextPure is the singleton reset on 0,1,3; at B it maps 0 and 4 to 4 and the other modes to 2.

S=ActualPair(p,q,r,O) is this subtype of State times Z, hence finite. The positive actual history [0] makes it nonempty. For every source-positive symbol the acquired cylinder quotient gives the literal positive extension mass, and the source and observer folds give nextPair. Thus every such successor is again in S. actualStep is this lifted successor on a positive source weight; on a zero source weight it chooses the present pair as an auxiliary endpoint. This choice changes no transition mass and does not change the total observer update.

K=pairMatrix(p,q,r,O) sums v(mode(t),y) over symbols with actualStep(O,t,y)=u. Here v(i,y)=pureRow(p,q,r,i,y). It is the stochastic matrix on the actual subtype S. ClosedClass(K) means an actual terminal communicating class of the positive support, including reachability by the empty path. ClassStates(C) is its finite state set. The theorem quantifies every such class, proves it nonempty and irreducible, and supplies closure under every positive support path.

For a pair t, let aH(t) be the Bhattacharyya affinity of its pure source H-word law and the observer generated H-word law, and d(t,y)=sqrt(v(mode(t),y)*row(O,configuration(t),y)). The independently defined word laws give a(H+1)(t)=sum_y d(t,y)*aH(nextPair(O,t,y)). Nonnegativity and normalized row affinity make aH decrease from one, so its infimum l(t) is a limit and satisfies the same finite-sum equation. The Hellinger-to-TV lower bracket and the actual-history guarantee imply l(t)>=1-epsilon>0 on S. Source-zero symbols have d(t,y)=0, even if the observer gives them positive weight.

Fix any actual terminal class and maximize l there, with maximum M>0. Closure gives l(nextPair)<=M on every source-positive symbol. Therefore M=sum_y d*l(nextPair)<=M*sum_y d<=M. Equality forces sum_y d=1; normalized Hellinger separation then forces the observer row to equal the complete source row, including its zeros. The nonnegative weighted deficits M-l(nextPair) sum to zero. At an exact row every source-positive coefficient is positive, so each such successor also has limiting affinity M. Actual communication propagates this equality to every pair of the class, forcing every row exact.

With exact rows, induction on the complete future word length gives generatedLaw(O,configuration(t))=pureLaw(p,q,r,mode(t)). A source-zero first symbol makes both word weights zero; a positive first symbol stays inside the class, where the induction applies. This proves equality at every finite horizon without conditioning on a forecast-positive event or discarding generated words.

The positive square edges connect 0,1,2,3 and the positive leaf edges connect 0 and 4. More explicitly, any mode reaches 0 using singleton reads, with mode 2 first reading 1; from 0 the words [], [1], [1,B], [3], [B] reach modes 0,1,2,3,4. These paths lift inside every actual closed class. Choosing one pair above each mode gives actually reachable configurations. Existing full-domain pure-profile separation makes these five configurations distinct. The result does not assert a minimum observer cardinality, exactness of transient configurations, or uniqueness of the recurrent presentation.

**Definition 1.1 (Synchronized).**

$$\forall Z \in \operatorname{Type}\left(\right),\; \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall t \in \operatorname{Prod}\left(\operatorname{State}\left(\right), Z\right),\; \operatorname{Synchronized}\left(p, q, r, O, t\right) \Leftrightarrow \left(\exists h \in \operatorname{List}\left(\operatorname{Visible}\left(\right)\right),\; \left(\left(0 < \operatorname{historyMass}\left(p, q, r, h\right) \land \left(\exists y \in \operatorname{Visible}\left(\right),\; \operatorname{Member}\left(y, h\right) \land y \ne \operatorname{B}\left(\right)\right)\right) \land \operatorname{sourceRun}\left(h\right) = \operatorname{pure}\left(\operatorname{mode}\left(t\right)\right)\right) \land \operatorname{run}\left(\operatorname{toObserver}\left(O\right), h\right) = \operatorname{configuration}\left(t\right)\right)$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.Synchronized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition uses the full fixed source and actual acquired histories.

**Definition 1.2 (ActualPair).**

$$\forall Z \in \operatorname{Type}\left(\right),\; \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \operatorname{ActualPair}\left(p, q, r, O\right) = \operatorname{Subtype}\left(\operatorname{Prod}\left(\operatorname{State}\left(\right), Z\right), \operatorname{Synchronized}\left(p, q, r, O\right)\right)$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.ActualPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition uses the full fixed source and actual acquired histories.

**Definition 1.3 (nextPair).**

$$\forall Z \in \operatorname{Type}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall t \in \operatorname{Prod}\left(\operatorname{State}\left(\right), Z\right),\; \forall y \in \operatorname{Visible}\left(\right),\; \operatorname{nextPair}\left(O, t, y\right) = \operatorname{Pair}\left(\operatorname{nextPure}\left(\operatorname{mode}\left(t\right), y\right), \operatorname{update}\left(O, \operatorname{configuration}\left(t\right), y\right)\right)$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.nextPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition uses the full fixed source and actual acquired histories.

**Definition 1.4 (actualStep).**

$$\forall Z \in \operatorname{Type}\left(\right),\; \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall t \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \forall y \in \operatorname{Visible}\left(\right),\; \operatorname{actualStep}\left(O, t, y\right) = \operatorname{ifThenElse}\left(0 < \operatorname{pureRow}\left(p, q, r, \operatorname{mode}\left(\operatorname{val}\left(t\right)\right), y\right), \operatorname{lift}\left(\operatorname{nextPair}\left(O, \operatorname{val}\left(t\right), y\right)\right), t\right)$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.actualStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lift carries the derived actual-history membership proof; its proof argument is suppressed.

**Definition 1.5 (pairMatrix).**

$$\forall Z \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(Z\right)] \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall t \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \forall u \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \operatorname{entry}\left(\operatorname{pairMatrix}\left(p, q, r, O\right), t, u\right) = \sum_{y\in \operatorname{Visible}\left(\right)} \operatorname{ifThenElse}\left(\operatorname{actualStep}\left(O, t, y\right) = u, \operatorname{pureRow}\left(p, q, r, \operatorname{mode}\left(\operatorname{val}\left(t\right)\right), y\right), 0\right)$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.pairMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition uses the full fixed source and actual acquired histories.

**Theorem 1.6 (recurrent pair rigidity).**

$$\forall Z \in \operatorname{Type}\left(\right),\; [\operatorname{Fintype}\left(Z\right)] \forall p \in \operatorname{Real}\left(\right),\; \forall q \in \operatorname{Real}\left(\right),\; \forall r \in \operatorname{Real}\left(\right),\; \forall O \in \operatorname{GeneratedObserver}\left(Z\right),\; \forall epsilon \in \operatorname{Real}\left(\right),\; \left(\left(\operatorname{admissible}\left(p, q, r\right) \land \mathit{epsilon} < 1\right) \land \left(\forall h \in \operatorname{List}\left(\operatorname{Visible}\left(\right)\right),\; 0 < \operatorname{historyMass}\left(p, q, r, h\right) \Rightarrow \left(\forall H \in \operatorname{Nat}\left(\right),\; 0 < H \Rightarrow \operatorname{totalVariation}\left(\operatorname{atHorizon}\left(\operatorname{actualFutureWordWeight}\left(p, q, r, h\right), H\right), \operatorname{atHorizon}\left(\operatorname{generatedLaw}\left(\operatorname{update}\left(O\right), \operatorname{row}\left(O\right), \operatorname{run}\left(\operatorname{toObserver}\left(O\right), h\right)\right), H\right)\right) \le \mathit{epsilon}\right)\right)\right) \Rightarrow \left(\left(\left(\left(\left(\left(\operatorname{Nonempty}\left(\operatorname{ActualPair}\left(p, q, r, O\right)\right) \land \left(\forall h \in \operatorname{List}\left(\operatorname{Visible}\left(\right)\right),\; \left(0 < \operatorname{historyMass}\left(p, q, r, h\right) \land \left(\exists y \in \operatorname{Visible}\left(\right),\; \operatorname{Member}\left(y, h\right) \land y \ne \operatorname{B}\left(\right)\right)\right) \Rightarrow \left(\exists t \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \operatorname{configuration}\left(\operatorname{val}\left(t\right)\right) = \operatorname{run}\left(\operatorname{toObserver}\left(O\right), h\right) \land \operatorname{acquiredPosterior}\left(p, q, r, h\right) = \operatorname{pureVector}\left(\operatorname{mode}\left(\operatorname{val}\left(t\right)\right)\right)\right)\right)\right) \land \left(\forall t \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \forall y \in \operatorname{Visible}\left(\right),\; 0 < \operatorname{pureRow}\left(p, q, r, \operatorname{mode}\left(\operatorname{val}\left(t\right)\right), y\right) \Rightarrow \operatorname{val}\left(\operatorname{actualStep}\left(O, t, y\right)\right) = \operatorname{nextPair}\left(O, \operatorname{val}\left(t\right), y\right)\right)\right) \land \operatorname{RowStochastic}\left(\operatorname{pairMatrix}\left(p, q, r, O\right)\right)\right) \land \operatorname{Nonempty}\left(\operatorname{ClosedClass}\left(\operatorname{pairMatrix}\left(p, q, r, O\right)\right)\right)\right) \land \left(\forall C \in \operatorname{ClosedClass}\left(\operatorname{pairMatrix}\left(p, q, r, O\right)\right),\; \left(\left(\left(\left(\operatorname{Nonempty}\left(\operatorname{ClassStates}\left(C\right)\right) \land \operatorname{IsIrreducible}\left(\operatorname{restriction}\left(\operatorname{pairMatrix}\left(p, q, r, O\right), \operatorname{ClassStates}\left(C\right)\right)\right)\right) \land \left(\forall t \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \operatorname{Member}\left(t, \operatorname{ClassStates}\left(C\right)\right) \Rightarrow \left(\forall u \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \operatorname{Reach}\left(\operatorname{pairMatrix}\left(p, q, r, O\right), t, u\right) \Rightarrow \operatorname{Member}\left(u, \operatorname{ClassStates}\left(C\right)\right)\right)\right)\right) \land \left(\forall t \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \operatorname{Member}\left(t, \operatorname{ClassStates}\left(C\right)\right) \Rightarrow \operatorname{row}\left(O, \operatorname{configuration}\left(\operatorname{val}\left(t\right)\right)\right) = \operatorname{pureRow}\left(p, q, r, \operatorname{mode}\left(\operatorname{val}\left(t\right)\right)\right)\right)\right) \land \left(\forall t \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \operatorname{Member}\left(t, \operatorname{ClassStates}\left(C\right)\right) \Rightarrow \operatorname{generatedLaw}\left(\operatorname{update}\left(O\right), \operatorname{row}\left(O\right), \operatorname{configuration}\left(\operatorname{val}\left(t\right)\right)\right) = \operatorname{pureLaw}\left(p, q, r, \operatorname{mode}\left(\operatorname{val}\left(t\right)\right)\right)\right)\right) \land \left(\forall i \in \operatorname{State}\left(\right),\; \exists t \in \operatorname{ActualPair}\left(p, q, r, O\right),\; \operatorname{Member}\left(t, \operatorname{ClassStates}\left(C\right)\right) \land \operatorname{mode}\left(\operatorname{val}\left(t\right)\right) = i\right)\right)\right) \land \left(\exists f \in \operatorname{Function}\left(\operatorname{State}\left(\right), Z\right),\; \operatorname{Injective}\left(f\right) \land \left(\forall i \in \operatorname{State}\left(\right),\; \operatorname{Member}\left(\operatorname{apply}\left(f, i\right), \operatorname{Reached}\left(\operatorname{toObserver}\left(O\right), p, q, r\right)\right) \land \operatorname{generatedLaw}\left(\operatorname{update}\left(O\right), \operatorname{row}\left(O\right), \operatorname{apply}\left(f, i\right)\right) = \operatorname{pureLaw}\left(p, q, r, i\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.recurrent_pair_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all admissible sources, all finite unrestricted normalized self-generated observers, and every real epsilon<1 satisfying the complete actual-history guarantee, all displayed conclusions hold simultaneously.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.ActualPair`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.Synchronized`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.actualStep`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.nextPair`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.pairMatrix`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/FiveModeRecurrentPairRigidity.recurrent_pair_rigidity`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClasses](../../Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClasses.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws](FiveModeSelfGeneratedLaws.md)
- Dependency: [D5/S3/TotalVariation/HellingerDivergence](../../TotalVariation/HellingerDivergence.md)
