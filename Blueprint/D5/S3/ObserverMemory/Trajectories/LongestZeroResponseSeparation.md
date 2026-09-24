# Uniform Direction Separation and Persistent Memory

## Abstract

Uniform actual-history separation and exact persistent-state bit lower bounds.

**Theorem 1.1 (Finite actual responses recover the parameters).**

Lean statement: `D5/S3/ObserverMemory/Trajectories/LongestZeroResponseSeparation.response_separates`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/LongestZeroResponseSeparation.response_separates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix r and two natural-valued functions h,g. Suppose both gap words have length span+1 at most R. They may start at different nonnegative positions p and p-prime. If their actual directions agree after every n from zero through R-5, measured from the respective word endpoints, then h(i)=g(i) for every i<r.

The exact response formula first recovers the length of the entire word: if the two first long intervals expired at different times, one response would still have the first-anchor parity when the other has the next-anchor parity. Their first mismatch occurs within the prescribed horizon. Equality of the total lengths lets the argument pass to the two tails; equality of tail lengths then recovers the first filler. This proves injectivity directly from actual outputs.

**Theorem 1.2 (A uniform actual-history family forces a state and bit lower bound).**

Lean statement: `D5/S3/ObserverMemory/Trajectories/LongestZeroResponseSeparation.source_family_separates`

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/LongestZeroResponseSeparation.source_family_separates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every R>=20 and k>=2, set q=floor(sqrt((R:Real)/5)). Then q>=2. Parameters range over all functions Fin(q-1)->Fin(q+1). Their window one positions are obtained from familyGaps(q-1) with left padding R-(span+1). The proof derives 5q^2<=R and the uniform fit bound; no fit or response-separation hypothesis is assumed.

Each resulting two-sided bit configuration is zero outside those finite one positions. It has no consecutive ones, hence no forbidden block of k ones for any k>=2. Positions R-1 and R-2 are respectively one and zero, so every initial grammar state is exactly one. Every subsequent bit at R+n is zero and is legal. Finite responses are the actual direction bits at current position R+n for n in Fin(R-4), namely n=0,...,R-5. Their map is injective and its image has exactly (q+1)^(q-1) elements.

History R k represents a complete legal past in physical coordinates, including arbitrary negative earlier positions. Its current position e satisfies R<=e; unread positions are canonically filled with zero and provide no future input. historyReadout applies the same complete-interval, longest/latest selector in [e-R,e) and counts every transport zero in (b,e). Thus at e=R+n the window is [n,R+n). Relative endpoints are obtained by subtracting e, and the closing anchor is b+1.

Extends H x H-prime means that the current position advances by one and precisely the newly read bit at the old current position becomes x. Both histories must be legal. For any finite state carrier S, any history map M, fixed updates T(false),T(true), and readout o satisfying o(M(H))=historyReadout(H) and M(H-prime)=T(x)(M(H)) on every legal extension, put N=card(range M). The theorem proves (q+1)^(q-1)<=N and (q-1)log_2(q+1)<=log_2 N<=ceil(log_2 N), with the first-to-ceiling inequality explicitly in its conclusion.

The history map may retain any information from the full past; it is not assumed to depend only on the window. All retained clock, phase, control, or history information must be represented in S. The updates and readout receive no separate current-position input, raw-window reread, or external phase. Appending zero is proved to satisfy Extends for every history. The padded histories are realized with their original bit configurations and current positions R+n, and their zero iterates and readouts are identified exactly with the finite responses.

The complete zero itinerary factors through M by prediction_completion_universality. Response injectivity therefore makes the parameter-to-reachable-state map injective. The finite cardinality inequality, monotonicity of logarithm base two, its power identity, and the ceiling inequality yield the stated bit bound. Only direction is observed; an exact representation that also determines input legality obeys the same lower bound.

Taking the minimum of the ceiling-log costs over either original class of finite exact representations preserves this bound. This uses their stated finite existence, supplied by the full window with the exact grammar state. No new minimum over the zero-only contract is substituted for either class. The observation horizon stops just before the final anchor expires at R-4; its subsequent default-zero output is not treated as a real-anchor switch.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/LongestZeroResponseSeparation.response_separates`
- Truth anchor: `D5/S3/ObserverMemory/Trajectories/LongestZeroResponseSeparation.source_family_separates`
- Dependency: [D5/S3/ObserverMemory/PredictionFactors/PredictionCompletionUniversality](../PredictionFactors/PredictionCompletionUniversality.md)
- Dependency: [D5/S3/ObserverMemory/Trajectories/LongestZeroSelectorResponse](LongestZeroSelectorResponse.md)
