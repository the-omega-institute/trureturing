# Saturated Control Region

## Abstract

An attained maximal cumulative cost produces an actual silent successor region covering every current source.

**Theorem 1.1 (A source-covering silent region without finite state assumptions).**

$$\forall d:\mathbb {N},((2\le d)\implies (\forall A:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall B:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall h:\operatorname {IsCompl}(A,B),(((0<\operatorname {finrank}(\operatorname {ZMod}(2),A))\land(0<\operatorname {finrank}(\operatorname {ZMod}(2),B)))\implies (\forall MA:Type_{u},(\forall MB:Type_{v},(\forall Root:Type_{w},(\forall C:\operatorname {Controller}(h,MA,MB,Root),(\forall K:\mathbb {N},((\operatorname {UniformCumulativeBudget}(C,K))\implies (\exists mstar:\operatorname {State}(C),(\exists i:\operatorname {Fin}(d),((\exists a:A,(\exists b:B,(\exists initialWord:\operatorname {List}(\operatorname {Action}(d)),(\operatorname {runWord}(\operatorname {step}(C),initialWord,\operatorname {initial}(C,a,b))=mstar))))\land(0<\operatorname {splitCost}(h,i))\land(\forall word:\operatorname {List}(\operatorname {Action}(d)),(\forall f:\operatorname {Action}(d),(\operatorname {cost}(C,\operatorname {runWord}(\operatorname {step}(C),word,mstar),f)=0)))\land(\forall word:\operatorname {List}(\operatorname {Action}(d)),(\forall f:\operatorname {Action}(d),(\exists nextWord:\operatorname {List}(\operatorname {Action}(d)),(\operatorname {step}(C,f,\operatorname {runWord}(\operatorname {step}(C),word,mstar))=\operatorname {runWord}(\operatorname {step}(C),nextWord,mstar)))))\land(\forall z:\operatorname {Source}(d),(\exists word:\operatorname {List}(\operatorname {Action}(d)),(\operatorname {readout}(C,\operatorname {runWord}(\operatorname {step}(C),word,mstar))=z)))\land(\forall a:A,(\forall b:B,(\operatorname {node}(\operatorname {protocol}(C,\operatorname {rewrite}(i),\operatorname {rootA}(C,\operatorname {rewrite}(i),\operatorname {initA}(C,a))),\operatorname {nil}())\neq \operatorname {inr}(\operatorname {unit}()))))\land(\forall word:\operatorname {List}(\operatorname {Action}(d)),(\operatorname {node}(\operatorname {protocol}(C,\operatorname {rewrite}(i),\operatorname {rootA}(C,\operatorname {rewrite}(i),\operatorname {fst}(\operatorname {val}(\operatorname {runWord}(\operatorname {step}(C),word,mstar))))),\operatorname {nil}())=\operatorname {inr}(\operatorname {unit}())))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/SaturatedControlRegion.saturated_silent_source_region` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the original data and control source, a complementary pair of positive-dimensional original submodules, and a compliant endpoint controller with arbitrary persistent local and root types. Assume one natural cumulative-cost bound for every locally initialized original input and every finite action word.

There is an initialized reachable state whose entire finite-word successor region is closed under all original actions. Every edge in that same region has zero communication cost, and its current readouts cover the entire original source.

Some original rewrite has positive initial cost. Its public roots are internal on the full local initialization product and leaves throughout that very silent region. Root agreement transfers these properties to either endpoint's local root selector.

A bounded nonempty set of attained natural costs has a greatest attained value. A positive-cost successor appended to its attaining word contradicts maximality. Total original basis translations generate a finite word reaching every desired current source from the attained state. Both arguments use actual protocol-realized states rather than a finite-state cycle criterion or an assumed product of later endpoints.

This supplier supports persistent-state separation and the arbitrary-carrier memory lower bounds. It does not supply the restricted attaining controller, the memory embeddings, the exact first-rewrite cost on all words, or the storage minima.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/SaturatedControlRegion.saturated_silent_source_region`
- Dependency: [D5/S3/ObserverMemory/Algorithms/FixedSplitRewriteBudget](FixedSplitRewriteBudget.md)
