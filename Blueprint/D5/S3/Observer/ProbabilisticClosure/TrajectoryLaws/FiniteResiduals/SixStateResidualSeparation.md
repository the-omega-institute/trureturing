# Six-state separation of archives and joint residuals

## Abstract

The same normalized six-state process has identical stopping archives, distinct permanent residuals, and no almost-sure label update.

The states s,t,u,v,w,z are Fin(6) indices 0,1,2,3,4,5, and labels 0,1 are false,true. The complete nonzero joint kernel is: s to (0,u) and (0,v), each one half; t to (0,w), mass one; u to (0,z), mass one; v to (1,z), mass one; w to (0,z) and (1,z), each one half; z to (0,z), mass one. Every omitted entry is zero. The rows are nonnegative and normalized. The ordinary absorbing state z can continue forever. All current observations are constant, the unique action is everywhere legal, and there is no failure or extra control.

The original recursive residual is used throughout. firstClass has fibers {s,t,u,z}, {v}, {w}, and equality of firstClass is exactly residual(K,1). stableClass has fibers {s}, {t}, {u,z}, {v}, {w}, and equality of stableClass is exactly residual(K,2). The six signatures using the first-stage classes are: s gives half (0,Czero) plus half (0,Cone); t gives (0,Chalf); u and z give (0,Czero); v gives (1,Czero); w gives half (0,Czero) plus half (1,Czero). Hence s and t agree at the first stage and differ at the second. The only nonsingleton second-stage fiber is {u,z}; both rows send mass one to (0,{u,z}). The next refinement equals the second, and induction gives residual(K,n+2)=residual(K,2) for every n. Its intersection over all horizons is exactly stableClass equality.

For z, an all-zero word has mass one and every other word mass zero, by induction on word length. From s and t the empty word and one-letter word 0 have mass one; the one-letter word 1 has mass zero. A word of length at least two has mass one half exactly when its first letter is 0 and every letter after its second is 0. Thus 00 and 01 each have mass one half, and each may be followed only by zeroes. This computes the same all-depth profile from the same kernel at both initial states. The operational characterization gives equality of every allowed stopping law at every finite horizon, although the second and limiting residuals separate s and t.

representative selects s,t,u,v,w for the five stableClass values. quotientRow(q,(y,d)) sums the original row from representative(q) over successors with stableClass d. The proof checks that every original representative x gives exactly quotientRow(stableClass(x),(y,d)); the only distinct representatives of one fiber are u,z. Summing over y and d gives one, and all entries are nonnegative. StochasticQuotient includes both this normalized joint kernel and the exact identification of stableClass fibers with the original limiting residual. This is a stochastic quotient of the same process, not a separately selected model.

For any proposed deterministic update, updateFailure(update,x) is the sum of the actual original joint masses of branches whose successor class differs from update(stableClass(x),label). From s the two successful branches (0,u) and (0,v) each have mass one half and distinct successor classes. One predicted class cannot equal both; consequently updateFailure(update,s) is at least one half. In particular it cannot be zero, which rules out the update even almost surely. Zero-mass branches are retained in the sum and contribute zero.

claim is the disjunction of two assertions about this one process. The first says that for every pair of states, equality of every finite stopping experiment at every horizon entails equality of the recursive residuals at every horizon. The second says that StochasticQuotient entails existence of a deterministic update with updateFailure zero at every state. Refuting this disjunction refutes each assertion separately: the first uses the all-depth stopping premise at s,t and their actual second-stage separation; the second uses the actual normalized stochastic quotient and the positive update-failure bound.

**Theorem 1.1 (Complete same-kernel correction).**

$$(\forall x:\operatorname{Fin}(6), (\forall xp:\operatorname{Fin}(6), (\operatorname{residual}(kernel,1,x,xp)\Leftrightarrow\operatorname{firstClass}(x)=\operatorname{firstClass}(xp))))\land (\forall x:\operatorname{Fin}(6), (\forall xp:\operatorname{Fin}(6), (\operatorname{residual}(kernel,2,x,xp)\Leftrightarrow\operatorname{stableClass}(x)=\operatorname{stableClass}(xp))))\land (\forall n:Nat, (\operatorname{residual}(kernel,n+2)=\operatorname{residual}(kernel,2)))\land (\forall x:\operatorname{Fin}(6), (\forall xp:\operatorname{Fin}(6), ((\forall n:Nat, (\operatorname{residual}(kernel,n,x,xp)))\Leftrightarrow\operatorname{stableClass}(x)=\operatorname{stableClass}(xp))))\land (\forall w:\operatorname{List}(Bool), (\operatorname{wordProb}(kernel,0,w)=\operatorname{profile}(w)\land \operatorname{wordProb}(kernel,1,w)=\operatorname{profile}(w)))\land (\forall n:Nat, (\operatorname{StoppingEq}(kernel,n,0,1)))\land (\operatorname{residual}(kernel,1,0,1))\land (\neg \operatorname{residual}(kernel,2,0,1))\land (\neg (\forall n:Nat, (\operatorname{residual}(kernel,n,0,1))))\land (StochasticQuotient)\land (\forall update:\operatorname{Fin}(5)\Rightarrow Bool\Rightarrow \operatorname{Fin}(5), (\frac{1}{2}\leq\operatorname{updateFailure}(update,0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.counterkernel_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The conjunction gives both complete finite partitions, the permanent plateau and its limiting partition, the actual all-depth word profile and stopping equality, the first-stage agreement and second-stage and limiting separation, the normalized stochastic quotient, and the positive update-failure bound. Every occurrence of kernel denotes the single joint kernel specified above.

**Theorem 1.2 (Both withdrawn implications fail on the same kernel).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two cases of the disjunction are contradicted independently. The archive comparison uses the all-depth common word profile and the exact stopping theorem. The quotient comparison uses its representative independence and normalization before the update obstruction. Thus the random successor-class distribution is well defined, while the current class and observed label do not determine the realized successor class.

The valid implication from recursive residuals to finite archive laws remains. Equality of actual archive laws does not in general identify the recursive quotient or its claimed minimality, and it does not justify merging states in that quotient. No general stochastic factorization or decoder repair is asserted. A common decoder still pushes equal archive laws to equal response laws; identifying those responses with a semantic residual requires a separate characterization. Recursive sufficient-boundary claims must also preserve current observations. The example specifies no semantic event kernel, semantic residual or decoder, so it does not settle theorems under additional such hypotheses. Permission-delay, graft and coordinate-recovery claims retain their own menu, readout, successor and inverse-map conditions. None is proved or refuted here by association, and no physical or empirical consequence follows.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.counterkernel_facts`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/SixStateResidualSeparation.result`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping](FiniteResidualStopping.md)
