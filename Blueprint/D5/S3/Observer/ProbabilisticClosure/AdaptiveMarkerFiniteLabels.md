# Finite labels and causal acquired-prefix realization

## Abstract

Finite compatible two-arm labels realize a chronological stopped archive with its original seed.

**Theorem 1.1 (One supported completion realizes every prefix and the first stopping time).**

$$\forall U:Type, [\operatorname{MeasurableSpace}\left(U\right)]\Rightarrow\forall p:\operatorname{Policy}\left(U\right), \forall u:U, \forall w:Word, \operatorname{terminalFirstTrue}\left(w\right)\Rightarrow\operatorname{policyConformity}\left(p, u, w\right)\Rightarrow\forall z:\operatorname{Labels}\left(w\right), \begin{gathered}\operatorname{noAdjacentOnes}\left(\operatorname{completion}\left(z\right)\right)\land\\{}(\forall s:Bool, \forall i:\operatorname{Fin}\left(\operatorname{sideTotal}\left(w, s\right)+1\right), \operatorname{endpoint}\left(\operatorname{completion}\left(z\right), s, i\right)=\operatorname{bit}\left(z, s, i\right))\land\\{}(\forall k:\mathbb{N}, (k\leq \operatorname{length}\left(w\right))\Rightarrow\operatorname{actualRun}\left(p, u, \operatorname{completion}\left(z\right), k\right)=\operatorname{State}\left(\operatorname{reverse}\left(\operatorname{actions}\left(w, k\right)\right), \operatorname{reverse}\left(\operatorname{replies}\left(w, k\right)\right), \operatorname{decide}\left(k=\operatorname{length}\left(w\right)\right)\right))\land\\{}(\operatorname{actualRun}\left(p, u, \operatorname{completion}\left(z\right), \operatorname{length}\left(w\right)\right)=\operatorname{State}\left(\operatorname{reverse}\left(\operatorname{map}\left(fst, w\right)\right), \operatorname{reverse}\left(\operatorname{map}\left(snd, w\right)\right), true\right))\land\\{}(\operatorname{actualQueryCount}\left(p, u, \operatorname{completion}\left(z\right), \operatorname{length}\left(w\right)\right)=\operatorname{length}\left(w\right))\land\\{}(\operatorname{stoppingTime}\left(p, u, \operatorname{completion}\left(z\right)\right)=\operatorname{length}\left(w\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels.finite_label_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Word is a chronological List of pairs of a Boolean arm and a Boolean reply. The archive consists only of the original seed u and this word w; it contains neither a root bit nor an infinite source. False selects the left arm and true selects the right arm. For every natural k, actions(w,k) and replies(w,k) map the corresponding projections over take(k,w). The policy receives their reversals, because actualRun stores acquired histories newest first.

terminalFirstTrue(w) requires positive length T and, for each zero-based index k below T, reply k equal to decide(k+1=T). policyConformity(p,u,w) requires action k to equal the same policy p evaluated at the original seed u and the reversed prefixes before k. The seed space is an arbitrary Type with an arbitrary measurable-space instance. No probability law, standard Borel assumption, or additional seed observation is used.

sideTotal(w,s) counts arm s in the whole action word, and occurrences(w,s,k) counts it in the prefix before k. A Labels(w) witness supplies, on each arm s, a Boolean label at every index from zero through sideTotal(w,s). The two labels at zero agree. Consecutive finite labels never both equal true. For every query k, its reply is exactly the 00 predicate of the labels at occurrences(w,s,k) and its successor, where s is that query's arm. Finite compatibility means that a Labels(w) witness exists; these auxiliary labels are witnesses of compatibility and are not additional archive fields. Their conditions contain no actualRun equation, source, execution witness, or inverse normal form.

extended(z,s,i) keeps every supplied finite label and is false for i beyond sideTotal(w,s). completion(z) has the common label at index zero as root and arm s entry i equal to extended(z,s,i+1). The theorem holds for every Labels witness, using that single completion at all depths. Fin indices in the label-preservation clause are coerced to natural endpoint indices. The last equality coerces T to WithTop Nat. Thus it identifies the first stopping time, as well as the complete terminal state and the number of acquired queries.

The causal induction reconstructs the state before each next policy choice. The reconstructed action and reply lists select the recorded arm, and its occurrence count selects the finite-label 00 response. Earlier prefixes remain active; the final prefix is stopped. The zero tail ensures global no-adjacent-ones support beyond both acquired arm lengths.

This finite realization establishes a support-level component of the common-parameter stopped-archive construction. It does not assert root recovery, an inverse normal form, opportunity enumeration, positive Markov cylinder mass, likelihood or posterior formulas, almost-sure termination, or measurability of the archive maps. Those require separate results.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerFiniteLabels.finite_label_realization`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails](AdaptiveMarkerStoppingTails.md)
