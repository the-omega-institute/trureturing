# Newman Determinant Threshold

## Abstract

Normalized Fredholm, total-positivity, and Stieltjes criteria define the same nondegenerate Newman completion threshold.

**Theorem 1.1 (The three normalized completion criteria have one threshold).**

$$\begin{gathered}\forall F, P_{\infty}, S: \mathbb{R} \to \operatorname{Prop},\\{}T_{F} := \left\{F(t) \mid t \in \mathbb{R}\right\},\\{}T_{P_{\infty}} := \left\{P_{\infty}(t) \mid t \in \mathbb{R}\right\},\\{}T_{S} := \left\{S(t) \mid t \in \mathbb{R}\right\},\\{}\Lambda_{F} := \operatorname{sInf}\left(T_{F}\right), \Lambda_{P_{\infty}} := \operatorname{sInf}\left(T_{P_{\infty}}\right), \Lambda_{S} := \operatorname{sInf}\left(T_{S}\right),\\{}{{{\forall t \in \mathbb{R}, {{F(t)} \iff {P_{\infty}(t)}} \land {{F(t)} \iff {S(t)}}} \land {\operatorname{Nonempty}\left(T_{F}\right)}} \land {\operatorname{BddBelow}\left(T_{F}\right)}} \Rightarrow {{{{{{{T_{F} = T_{P_{\infty}}} \land {T_{F} = T_{S}}} \land {\Lambda_{F} = \Lambda_{P_{\infty}}}} \land {\Lambda_{F} = \Lambda_{S}}} \land {\operatorname{IsGLB}\left(T_{F}, \Lambda_{F}\right)}} \land {\operatorname{IsGLB}\left(T_{P_{\infty}}, \Lambda_{P_{\infty}}\right)}} \land {\operatorname{IsGLB}\left(T_{S}, \Lambda_{S}\right)}}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Fredholm/NewmanDeterminantThreshold.newman_determinant_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real time, F, P_infinity, and S denote respectively the positive trace-class Fredholm representation criterion, the PF-infinity coefficient criterion, and the reciprocal-zero Stieltjes moment criterion. The pinned library has no countable trace-class determinant API, so these analytic criteria enter as typed predicates rather than as invented operator definitions.

The original unconditional equivalence is false: a PF-infinity generating function may contain an exponential factor, with exp(x) as the basic example, and therefore need not be a pure determinant det(I + x U). The displayed pointwise bridge is the necessary no-exponential-factor normalization hypothesis.

The Fredholm feasible-time set is required to be nonempty and bounded below. These premises prevent Lean's real convention sInf(empty) = 0 from turning the threshold into a silent degenerate value.

Pointwise equivalence gives equality of all three feasible-time sets. Congruence of sInf gives the threshold identities, while Mathlib's isGLB_csInf proves that every displayed threshold is the genuine greatest lower bound. A companion theorem transports feasible-time witnesses in every direction.

## References

- Truth anchor: `D5/S3/Weil/Fredholm/NewmanDeterminantThreshold.newman_determinant_threshold`
