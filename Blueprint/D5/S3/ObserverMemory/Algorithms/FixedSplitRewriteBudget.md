# Sharp rewrite budget for a fixed split

## Abstract

The same noncentral direct sum has sharp worst initial rewrite cost one or two, and every persistent cumulative controller obeys that lower bound.

**Definition 1.1 (Cost of an original data rewrite).**

$$\forall d:\mathbb {N},(\forall A:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall B:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall h:\operatorname {IsCompl}(A,B),((\operatorname {pA}()=\operatorname {projectionOnto}(A,B,h))\land(\operatorname {pB}()=\operatorname {projectionOnto}(B,A,\operatorname {symm}(h)))\land(\forall S:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\operatorname {ell}(S)=\operatorname {compose}(\operatorname {sndLinearMap}(),\operatorname {subtype}(S))))\land(\forall i:\operatorname {Fin}(d),(\operatorname {splitCost}(h,i)=\operatorname {rewriteCost}(\operatorname {ell}(A),\operatorname {ell}(B),\operatorname {pA}((\operatorname {single}(i,1),0)),\operatorname {pB}((\operatorname {single}(i,1),0)))))\land(\operatorname {Cstar}(h)=\operatorname {sup}(\operatorname {univ}(\operatorname {Fin}(d)),i\mapsto \operatorname {splitCost}(h,i)))\land(\forall K:\mathbb {N},(\operatorname {InitialRewriteBudget}(h,K)\iff (\forall i:\operatorname {Fin}(d),(\exists p:\operatorname {EndpointProtocol}(A,B,A,B),((\operatorname {RewriteCorrect}(\operatorname {ell}(A),\operatorname {ell}(B),\operatorname {pA}((\operatorname {single}(i,1),0)),\operatorname {pB}((\operatorname {single}(i,1),0)),\operatorname {id}(),\operatorname {id}(),p))\land(\forall a:A,(\forall b:B,(\forall n:\mathbb {N},(\forall t:\operatorname {Trace}(A,B),((\operatorname {execute}(\operatorname {answer}(),\operatorname {policy}(p),n,\operatorname {nil}(),(a,b))=\operatorname {some}((t,\operatorname {unit}())))\implies (\operatorname {length}(t)\le K)))))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget.splitCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Keep the original direct sum and its projections fixed. The data basis column on each side and the opposite control restriction determine the two required direction indicators. Their sum is the exact initial rewrite cost. Cstar is the finite supremum over all original data columns.

**Definition 1.2 (One bound for all initialized action words).**

$$\forall d:\mathbb {N},(\forall A:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall B:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall h:\operatorname {IsCompl}(A,B),(\forall MA:Type_{u},(\forall MB:Type_{v},(\forall Root:Type_{w},(\forall C:\operatorname {Controller}(h,MA,MB,Root),(\forall K:\mathbb {N},(\operatorname {UniformCumulativeBudget}(C,K)\iff (\forall a:A,(\forall b:B,(\forall word:\operatorname {List}(\operatorname {Action}(d)),(\operatorname {Comm}(\operatorname {step}(C),\operatorname {cost}(C),\operatorname {initial}(C,a,b),word)\le K)))))))))))))$$

*Formalization.* `D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget.UniformCumulativeBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A uniform cumulative budget quantifies every original local summary pair and every finite word in the complete original action alphabet. Costs use Comm on the actual operational state subtype and its protocol-realized step and bit-length cost.

**Theorem 1.3 (Classification and necessary persistent budget).**

$$\forall d:\mathbb {N},(\forall A:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall B:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall h:\operatorname {IsCompl}(A,B),(((2\le d)\land(0<\operatorname {finrank}(\operatorname {ZMod}(2),A))\land(0<\operatorname {finrank}(\operatorname {ZMod}(2),B)))\implies (((\operatorname {ell}(A)=0)\implies (\operatorname {Cstar}(h)=1))\land((\operatorname {ell}(B)=0)\implies (\operatorname {Cstar}(h)=1))\land((\operatorname {ell}(A)\neq 0)\implies ((\operatorname {ell}(B)\neq 0)\implies (\operatorname {Cstar}(h)=2)))\land(\exists i:\operatorname {Fin}(d),(0<\operatorname {splitCost}(h,i)))\land(\operatorname {IsLeast}(\{K:\mathbb {N}\mid \operatorname {InitialRewriteBudget}(h,K)\},\operatorname {Cstar}(h)))\land(\forall MA:Type_{u},(\forall MB:Type_{v},(\forall Root:Type_{w},(\forall C:\operatorname {Controller}(h,MA,MB,Root),(\forall K:\mathbb {N},((\operatorname {UniformCumulativeBudget}(C,K))\implies ((\operatorname {Cstar}(h)\le K)\land(\forall a:A,(\forall b:B,(\forall i:\operatorname {Fin}(d),((\operatorname {directionDemand}(\operatorname {pA}((\operatorname {single}(i,1),0)),\operatorname {ell}(B))\le \operatorname {rightCount}(\operatorname {trace}(C,\operatorname {rewrite}(i),\operatorname {initial}(C,a,b))))\land(\operatorname {directionDemand}(\operatorname {pB}((\operatorname {single}(i,1),0)),\operatorname {ell}(A))\le \operatorname {leftCount}(\operatorname {trace}(C,\operatorname {rewrite}(i),\operatorname {initial}(C,a,b))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget.fixed_split_rewrite_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every data dimension at least two and every fixed complementary pair of original submodules of positive dimensions, Cstar is one if either control restriction is zero and two if both restrictions are nonzero. There is at least one rewrite of positive cost. Cstar is the least uniform budget for correct initial rewrite protocols on all original summary pairs.

For any compliant persistent controller with arbitrary local and root types, every initial rewrite execution pays both directional indicators, and every uniform cumulative budget K satisfies Cstar at most K. Full local-product initialization makes each action root constant; composing the local leaf updates with their fixed readouts gives a prepared-input rewrite protocol without transporting or exposing query labels.

The classification uses the same fixed projections. With control on one side, a nonzero vector in the opposite summand lies in data space, so some projected data column is nonzero. With both restrictions nonzero, choose control-one vectors in both summands. Their sum lies in data space. If every left projected data column had zero control, linearity would contradict the chosen left control-one vector. A column with nonzero left control also has a nonzero right projection because its total control is zero.

This statement supplies the initial-rewrite budget lower bound and the classification required by the persistent theorem. It does not assert the restricted persistent-state construction, saturated silent successors, memory lower embeddings, exact all-word first- rewrite costs, storage minima, or completion of the full original theorem.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget.UniformCumulativeBudget`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget.fixed_split_rewrite_budget`
- Truth anchor: `D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget.splitCost`
- Dependency: [D5/S3/ObserverMemory/Algorithms/ControlRewriteDirectionalBound](ControlRewriteDirectionalBound.md)
