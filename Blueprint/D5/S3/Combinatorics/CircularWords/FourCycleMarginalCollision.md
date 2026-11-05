# Marginals and Paired Circular Readings

## Abstract

Individual circular-deletion marginals fail to determine a finite probability law, while paired readings from the same sample distinguish the exhibited laws.

Take actual Cycle(Nat) states X1=0123, X2=0321, Y1=0132, Y2=0231 modulo rotation, retaining orientation. Let mu assign one half to each X state, and nu assign one half to each Y state, with all other masses zero. Use rational Finsupp masses. J02(C)=(delete(0,C),delete(2,C)) records two observations from the same sample. pairedEvent is the indicator of {J02(X1),J02(X2)}.

**Theorem 1.1 (Equal Four Marginals and Disjoint Laws).**

$$(\forall C \in \mathrm{Cycle}\left(\mathrm{Nat}\right),\; (C \in \mathrm{union}\left(\mathrm{support}\left(mu\right), \mathrm{support}\left(nu\right)\right)) \Rightarrow ((\mathrm{Nodup}\left(C\right)) \land (\mathrm{toFinset}\left(C\right) = \mathrm{set}\left(0, 1, 2, 3\right)))) \land ((\forall C \in \mathrm{Cycle}\left(\mathrm{Nat}\right),\; (0 \le \mathrm{mu}\left(C\right)) \land (0 \le \mathrm{nu}\left(C\right))) \land ((\mathrm{mass}\left(mu\right) = 1) \land ((\mathrm{mass}\left(nu\right) = 1) \land ((\mathrm{Disjoint}\left(\mathrm{support}\left(mu\right), \mathrm{support}\left(nu\right)\right)) \land ((\forall i \in \mathrm{Nat},\; (i \in \mathrm{set}\left(0, 1, 2, 3\right)) \Rightarrow (\mathrm{push}\left(\mathrm{delete}\left(i\right), mu\right) = \mathrm{push}\left(\mathrm{delete}\left(i\right), nu\right))) \land ((\mathrm{eventProbability}\left(\mathrm{J02}, mu\right) = 1) \land (\mathrm{eventProbability}\left(\mathrm{J02}, nu\right) = 0)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CircularWords/FourCycleMarginalCollision.actual_marginal_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both supports consist of nodup circles with support {0,1,2,3}. Both masses are nonnegative and normalized, and the supports are disjoint. For deletion labels 0,1,2,3, the residual pairs of X states respectively are (123,132), (023,032), (013,031), (012,021), using canonical rotations. The Y states give respectively (132,123), (032,023), (013,031), (012,021). Hence all four pushforward marginals agree. The paired readings are X1:(123,013), X2:(132,031), Y1:(132,013), Y2:(123,031). The indicated event therefore has probabilities one and zero. No independence is assumed, and these two observations are not claimed to reconstruct every state or law.

For probability measures use TV(mu,nu)=sup_E |mu(E)-nu(E)|=one half of the L1 distance. The original laws and their J02 pushforwards each have TV distance one. The unhalved signed variation norm is two.

The finite signed mass space V is additive; its probability simplex M is a subset, not an additive group. Each pushforward q_i is directly Mathlib Finsupp.mapDomain.addMonoidHom(delete(i)). v=mu-nu is nonzero, for v(X1)=one half, lies in M-M, and satisfies q_i(v)=0 for all four labels. Apply ModelRelativeCompletenessDifferenceCriterion.model_relative_completeness_difference_criterion directly to V,q,M; M is nonempty because it contains mu. This is the nonzero intersection of the joint additive residual with the model difference set. The concrete laws are defined on Cycle(Nat). Identifying them with laws on the fixed-support subtype SupportedCircle({0,1,2,3}) is a hand correspondence: the generic criterion application was compiled, but the concrete subtype reindexing and its model-difference witness were not compiled as a concrete theorem. For three preselected distinct labels on a support of at least four, ThreeSpecifiedDeletions.reconstruct_three instead gives injectivity of the same-sample triple map. Apply Finsupp.mapDomain_injective directly to identify all finite signed laws, and hence probability laws, from that joint pushforward. Equality of a marginal family is a different condition.

## References

- Truth anchor: `D5/S3/Combinatorics/CircularWords/FourCycleMarginalCollision.actual_marginal_collision`
- Dependency: [D5/S3/Combinatorics/CircularWords/CircularDeletionTransport](CircularDeletionTransport.md)
