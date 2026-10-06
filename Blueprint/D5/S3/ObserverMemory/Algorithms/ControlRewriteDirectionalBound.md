# Control rewrite directional communication

## Abstract

Every correct endpoint-local rewrite pays the required directions on each actual execution, and a fixed exchange attains both bounds.

**Definition 1.1 (Both original rewrite outputs after local preparation).**

$$\forall A:Type_{u},(\forall B:Type_{v},(((\operatorname {AddCommGroup}(A))\land(\operatorname {Module}(\operatorname {ZMod}(2),A))\land(\operatorname {AddCommGroup}(B))\land(\operatorname {Module}(\operatorname {ZMod}(2),B)))\implies (\forall MA:Type_{w},(\forall MB:Type_{x},(\forall ellA:\operatorname {LinearMap}(\operatorname {ZMod}(2),A,\operatorname {ZMod}(2)),(\forall ellB:\operatorname {LinearMap}(\operatorname {ZMod}(2),B,\operatorname {ZMod}(2)),(\forall alpha:A,(\forall beta:B,(\forall initA:(A)\to (MA),(\forall initB:(B)\to (MB),(\forall p:\operatorname {EndpointProtocol}(MA,MB,A,B),(\operatorname {RewriteCorrect}(ellA,ellB,alpha,beta,initA,initB,p)\iff ((\forall a:A,(\forall b:B,(\exists n:\mathbb {N},(\exists t:\operatorname {Trace}(MA,MB),(\operatorname {execute}(\operatorname {answer}(),\operatorname {policy}(p),n,\operatorname {nil}(),(\operatorname {apply}(initA,a),\operatorname {apply}(initB,b)))=\operatorname {some}((t,\operatorname {unit}())))))))\land(\forall a:A,(\forall b:B,(\forall n:\mathbb {N},(\forall t:\operatorname {Trace}(MA,MB),((\operatorname {execute}(\operatorname {answer}(),\operatorname {policy}(p),n,\operatorname {nil}(),(\operatorname {apply}(initA,a),\operatorname {apply}(initB,b)))=\operatorname {some}((t,\operatorname {unit}())))\implies ((\operatorname {outA}(p,\operatorname {apply}(initA,a),\operatorname {bits}(t))=\operatorname {smul}(\operatorname {apply}(ellA,a)+\operatorname {apply}(ellB,b),alpha))\land(\operatorname {outB}(p,\operatorname {apply}(initB,b),\operatorname {bits}(t))=\operatorname {smul}(\operatorname {apply}(ellA,a)+\operatorname {apply}(ellB,b),beta)))))))))))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound.RewriteCorrect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original summary types are modules over ZMod 2, with control restrictions ellA and ellB and prescribed projection columns alpha and beta. Preparation maps them into arbitrary persistent local types. Correctness requires finite termination on every prepared pair and local outputs equal to (ellA(a)+ellB(b)) times their respective prescribed column.

**Definition 1.2 (The exact zero, one or two bit exchange).**

$$\forall A:Type_{u},(\forall B:Type_{v},(((\operatorname {AddCommGroup}(A))\land(\operatorname {Module}(\operatorname {ZMod}(2),A))\land(\operatorname {AddCommGroup}(B))\land(\operatorname {Module}(\operatorname {ZMod}(2),B)))\implies (\forall ellA:\operatorname {LinearMap}(\operatorname {ZMod}(2),A,\operatorname {ZMod}(2)),(\forall ellB:\operatorname {LinearMap}(\operatorname {ZMod}(2),B,\operatorname {ZMod}(2)),(\forall alpha:A,(\forall beta:B,(\forall p:\operatorname {EndpointProtocol}(A,B,A,B),((p=\operatorname {rewriteProtocol}(ellA,ellB,alpha,beta))\implies ((\operatorname {directionDemand}(alpha,ellB)=\operatorname {if}((alpha\neq 0)\land(ellB\neq 0),1,0))\land(\operatorname {directionDemand}(beta,ellA)=\operatorname {if}((beta\neq 0)\land(ellA\neq 0),1,0))\land(\operatorname {rewriteCost}(ellA,ellB,alpha,beta)=\operatorname {directionDemand}(alpha,ellB)+\operatorname {directionDemand}(beta,ellA))\land(p=\operatorname {rewriteProtocol}(ellA,ellB,alpha,beta))\land(\forall h:\operatorname {List}(\operatorname {Bool}()),(\operatorname {node}(p,h)=\operatorname {if}(((alpha\neq 0)\land(ellB\neq 0))\land(\operatorname {length}(h)=0),\operatorname {inl}(\operatorname {inr}(b\mapsto \operatorname {decide}(\operatorname {apply}(ellB,b)=1))),\operatorname {if}(((beta\neq 0)\land(ellA\neq 0))\land(\operatorname {length}(h)=\operatorname {if}((alpha\neq 0)\land(ellB\neq 0),1,0)),\operatorname {inl}(\operatorname {inl}(a\mapsto \operatorname {decide}(\operatorname {apply}(ellA,a)=1))),\operatorname {inr}(\operatorname {unit}())))))\land(\forall a:A,(\forall h:\operatorname {List}(\operatorname {Bool}()),(\operatorname {outA}(p,a,h)=\operatorname {if}(alpha=0,0,\operatorname {smul}(\operatorname {apply}(ellA,a)+\operatorname {if}(ellB=0,0,\operatorname {if}(\operatorname {getD}(\operatorname {get}(h,0),\operatorname {false}()),1,0)),alpha)))))\land(\forall b:B,(\forall h:\operatorname {List}(\operatorname {Bool}()),(\operatorname {outB}(p,b,h)=\operatorname {if}(beta=0,0,\operatorname {smul}(\operatorname {apply}(ellB,b)+\operatorname {if}(ellA=0,0,\operatorname {if}(\operatorname {getD}(\operatorname {get}(h,\operatorname {if}((alpha\neq 0)\land(ellB\neq 0),1,0)),\operatorname {false}()),1,0)),beta))))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound.rewriteProtocol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The right endpoint sends its old control contribution precisely when alpha is nonzero and ellB is nonzero. The left endpoint sends its old contribution precisely when beta is nonzero and ellA is nonzero. The public order is right then left. A zero column produces zero locally; a zero remote restriction supplies a zero contribution locally. Both old summaries remain available until the leaf outputs commit. In the formulas get(h,j) is the optional list entry, and getD supplies false when it is absent; if(condition,x,y) is x when the condition holds and y otherwise.

**Theorem 1.3 (Sharp directions on every execution).**

$$\forall A:Type_{u},(\forall B:Type_{v},(((\operatorname {AddCommGroup}(A))\land(\operatorname {Module}(\operatorname {ZMod}(2),A))\land(\operatorname {AddCommGroup}(B))\land(\operatorname {Module}(\operatorname {ZMod}(2),B)))\implies (\forall ellA:\operatorname {LinearMap}(\operatorname {ZMod}(2),A,\operatorname {ZMod}(2)),(\forall ellB:\operatorname {LinearMap}(\operatorname {ZMod}(2),B,\operatorname {ZMod}(2)),(\forall alpha:A,(\forall beta:B,((\forall MA:Type_{w},(\forall MB:Type_{x},(\forall p:\operatorname {EndpointProtocol}(MA,MB,A,B),(\forall a:MA,(\forall b:MB,(\forall n:\mathbb {N},(\forall t:\operatorname {Trace}(MA,MB),((\operatorname {execute}(\operatorname {answer}(),\operatorname {policy}(p),n,\operatorname {nil}(),(a,b))=\operatorname {some}((t,\operatorname {unit}())))\implies (\operatorname {PublicTrace}(p,\operatorname {nil}(),t))))))))))\land(\forall MA:Type_{w},(\forall MB:Type_{x},(\forall p:\operatorname {EndpointProtocol}(MA,MB,A,B),(\forall a:MA,(\forall b:MB,(\forall n:\mathbb {N},(\forall m:\mathbb {N},(\forall t:\operatorname {Trace}(MA,MB),(\forall s:\operatorname {Trace}(MA,MB),(((\operatorname {execute}(\operatorname {answer}(),\operatorname {policy}(p),n,\operatorname {nil}(),(a,b))=\operatorname {some}((t,\operatorname {unit}())))\land(\operatorname {execute}(\operatorname {answer}(),\operatorname {policy}(p),m,\operatorname {nil}(),(a,b))=\operatorname {some}((s,\operatorname {unit}()))))\implies (t=s)))))))))))\land(\forall MA:Type_{w},(\forall MB:Type_{x},(\forall initA:(A)\to (MA),(\forall initB:(B)\to (MB),(\forall p:\operatorname {EndpointProtocol}(MA,MB,A,B),((\operatorname {RewriteCorrect}(ellA,ellB,alpha,beta,initA,initB,p))\implies (\forall a:A,(\forall b:B,(\forall n:\mathbb {N},(\forall t:\operatorname {Trace}(MA,MB),((\operatorname {execute}(\operatorname {answer}(),\operatorname {policy}(p),n,\operatorname {nil}(),(\operatorname {apply}(initA,a),\operatorname {apply}(initB,b)))=\operatorname {some}((t,\operatorname {unit}())))\implies ((\operatorname {directionDemand}(alpha,ellB)\le \operatorname {rightCount}(t))\land(\operatorname {directionDemand}(beta,ellA)\le \operatorname {leftCount}(t))\land(\operatorname {rewriteCost}(ellA,ellB,alpha,beta)\le \operatorname {length}(t))))))))))))))\land(\operatorname {RewriteCorrect}(ellA,ellB,alpha,beta,\operatorname {id}(),\operatorname {id}(),\operatorname {rewriteProtocol}(ellA,ellB,alpha,beta)))\land(\forall a:A,(\forall b:B,(\exists n:\mathbb {N},(\exists t:\operatorname {Trace}(A,B),((\operatorname {execute}(\operatorname {answer}(),\operatorname {policy}(\operatorname {rewriteProtocol}(ellA,ellB,alpha,beta)),n,\operatorname {nil}(),(a,b))=\operatorname {some}((t,\operatorname {unit}())))\land(\operatorname {rightCount}(t)=\operatorname {directionDemand}(alpha,ellB))\land(\operatorname {leftCount}(t)=\operatorname {directionDemand}(beta,ellA))\land(\operatorname {length}(t)=\operatorname {rewriteCost}(ellA,ellB,alpha,beta))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound.rewrite_directional_sharpness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every successful evaluator history has the publicly determined query label at each preceding Boolean prefix and ends at its public leaf. Successful executions on one input are independent of sufficient fuel. These clauses apply to arbitrary persistent endpoint types.

For every correct protocol and every prepared original input, right-to-left bit count is at least the indicator of alpha nonzero and ellB nonzero, and left-to-right count is at least the indicator of beta nonzero and ellA nonzero. Both bounds concern the same execution. Their sum is a lower bound on its total bit length.

If the right-to-left count were zero, fixing the left prepared state and changing the right original summary by a control-one vector preserves the entire finite path. All questions on that path read only the unchanged left state, so the same public leaf and left output contradict the prescribed nonzero change. The symmetric argument proves the other direction.

The fixed exchange is correct on every original input and attains both direction counts and their sum. Its successful witnesses use at most three units of evaluator fuel, including the public leaf. The lower bound permits arbitrary public trees with finite actual termination and imposes no global depth.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound.RewriteCorrect`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound.rewriteProtocol`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound.rewrite_directional_sharpness`
- Dependency: [D5/S3/ObserverMemory/Algorithms/InitializedControlProtocol](InitializedControlProtocol.md)
